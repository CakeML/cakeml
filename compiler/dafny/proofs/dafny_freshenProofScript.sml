(*
  Correctness proof and properties for freshen.
*)
Theory dafny_freshenProof
Libs
  preamble
Ancestors
  mlstring mlint dafny_ast dafny_semanticPrimitives
  dafny_evaluate dafny_evaluateProps dafny_freshen


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
  state_rel s t m m_old cnt ⇔
    s.clock = t.clock ∧ s.output = t.output ∧
    s.heap = t.heap ∧ s.heap_old = t.heap_old ∧
    locals_rel s.locals m t.locals ∧ map_inv m cnt ∧
    locals_rel s.locals_old m_old t.locals_old ∧ map_inv m_old cnt
End

Definition env_rel_def:
  env_rel env env' ⇔
    env'.is_running = env.is_running ∧
    env'.prog = freshen_program env.prog
End

(* simps *)

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

Triviality not_mem_map_lookup[simp]:
  ¬MEM snam xs ⇒ MAP (lookup ((snam,tnum)::ms)) xs = MAP (lookup ms) xs
Proof
  Induct_on ‘xs’ \\ gvs []
QED

(* Various trivialities *)

Triviality REVERSE_LENGTH:
  ∀xs ys. ys = REVERSE xs ⇒ LENGTH ys = LENGTH xs
Proof
  Induct using SNOC_INDUCT \\ gvs []
QED

Triviality ALL_DISTINCT_APPEND_COMM:
  ALL_DISTINCT (x ++ y) ⇔ ALL_DISTINCT (y ++ x)
Proof
  eq_tac \\ gvs [ALL_DISTINCT_APPEND]
  \\ rpt strip_tac \\ res_tac
QED

Triviality distinct_reverse_append:
  ALL_DISTINCT (REVERSE xs ++ REVERSE ys) ⇔ ALL_DISTINCT (xs ++ ys)
Proof
  gvs [ALL_DISTINCT_APPEND]
QED

Triviality map_fst_reverse_imp:
  MAP FST m = REVERSE ns ⇒ (∀n. MEM n ns ⇒ MEM n (MAP FST m))
Proof
  gvs []
QED

Triviality every_less_weaken:
  EVERY (λi. i < ub) (xs: num list) ∧ ub ≤ ub' ⇒
  EVERY (λi. i < ub') xs
Proof
  rpt strip_tac
  \\ irule EVERY_MONOTONIC
  \\ qexists ‘λi. i < ub’ \\ gvs []
QED

Triviality sorted_desc_cons_not_mem:
  SORTED $> ((x: num)::xs) ⇒ ¬MEM x xs
Proof
  strip_tac \\ gvs [greater_sorted_eq]
  \\ rpt strip_tac \\ res_tac \\ gvs []
QED

Triviality SORTED_DESC_EVERY:
  ∀(x: num) xs. SORTED $> (x::xs) ⇒ EVERY (λi. i < x) xs
Proof
  Induct_on ‘xs’ \\ rpt strip_tac \\ gvs []
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
  \\ irule MONO_EVERY \\ qexists ‘λi. i < h’ \\ gvs []
QED

Triviality UNZIP_LENGTH:
  ∀xs ys zs. UNZIP xs = (ys, zs) ⇒ LENGTH ys = LENGTH zs
Proof
  Induct \\ gvs []
QED

(* lookup *)

Triviality lookup_pop:
  snam ≠ var ⇒ lookup ((snam,tnum)::m) var = lookup m var
Proof
  gvs [lookup_def]
QED

Triviality lookup_append_eq:
  ∀n m₁ m₀.
    MEM n (MAP FST m₁) ⇒ lookup (m₁ ++ m₀) n = lookup m₁ n
Proof
  rpt strip_tac
  \\ gvs [lookup_def, ALOOKUP_APPEND]
  \\ Cases_on ‘ALOOKUP m₁ n’
  \\ gvs [ALOOKUP_NONE]
QED

Triviality not_mem_lookup_append_eq:
  ¬MEM n (MAP FST m₁) ⇒
  lookup (m₁ ++ [(n,cnt)] ++ m₀) n = «v» ^ toString cnt
Proof
  rpt strip_tac
  \\ gvs [lookup_def, ALOOKUP_APPEND]
  \\ ‘ALOOKUP m₁ n = NONE’ by (gvs [ALOOKUP_NONE])
  \\ asm_simp_tac std_ss []
QED

Triviality gen_map_lookup_append_eq:
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
  \\ irule gen_map_lookup_append_eq
  \\ rpt strip_tac \\ gvs []
QED

Triviality distinct_names_map_lookup:
  ¬MEM snam (MAP FST ms) ∧ ALL_DISTINCT (MAP FST ms) ⇒
  MAP (lookup ((snam,tnum)::ms)) (MAP FST ms) =
  MAP (lookup ms) (MAP FST ms)
Proof
  rpt strip_tac \\ gvs []
QED

Triviality gen_map_lookup_map_tostring:
  ALL_DISTINCT (MAP FST m) ⇒
  MAP (lookup m) (MAP FST m) = MAP (λi. «v» ^ toString i) (MAP SND m)
Proof
  Induct_on ‘m’ \\ rpt strip_tac \\ gvs []
  \\ rename [‘(h::m')’]
  \\ namedCases_on ‘h’ ["n num"] \\ gvs []
QED

Triviality map_lookup_map_tostring:
  ∀m₁ ns m₀.
    MAP FST m₁ = REVERSE ns ∧ ALL_DISTINCT (MAP FST m₁) ⇒
    MAP (lookup (m₁ ++ m₀)) ns =
    MAP (λi. «v» ^ toString i) (REVERSE (MAP SND m₁))
Proof
  rpt strip_tac
  \\ drule gen_map_lookup_map_tostring \\ strip_tac
  \\ drule map_fst_reverse_imp \\ strip_tac
  \\ drule map_lookup_append_eq
  \\ disch_then $ qspec_then ‘m₀’ assume_tac \\ gvs []
  \\ ‘ns = REVERSE (MAP FST m₁)’ by gvs []
  \\ last_x_assum kall_tac
  \\ gvs [MAP_REVERSE]
QED

Triviality distinct_nums_names:
  ALL_DISTINCT xs ⇒
  ALL_DISTINCT (MAP (λi. «v» ^ toString i) xs)
Proof
  strip_tac
  \\ irule ALL_DISTINCT_MAP_INJ
  \\ rw [mlstring_common_prefix, num_to_str_11]
QED

Triviality distinct_nums_names_append:
  ALL_DISTINCT (xs ++ ys) ⇒
  ALL_DISTINCT
    (MAP (λi. «v» ^ toString i) xs ++
     MAP (λi. «v» ^ toString i) ys)
Proof
  strip_tac
  \\ pure_rewrite_tac [GSYM MAP_APPEND]
  \\ gvs [distinct_nums_names]
QED

(* map_inv *)

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
  >- (gvs [lookup_def, strcat_thm, implode_def]
      \\ Cases_on ‘toString tnum’
      \\ drule num_to_str_not_nil \\ gvs [])
  \\ drule map_inv_cons \\ rpt strip_tac \\ gvs []
  \\ drule map_inv_pop \\ strip_tac
  \\ last_x_assum drule \\ disch_then $ qspec_then ‘var’ assume_tac
  \\ Cases_on ‘snam = var’
  \\ gvs [lookup_def, mlstring_common_prefix, num_to_str_11]
QED

Triviality map_inv_distinct:
  map_inv m cnt ⇒ ALL_DISTINCT (MAP SND m)
Proof
  Induct_on ‘m’ \\ rpt strip_tac \\ gvs [map_inv_def]
  \\ drule SORTED_TL \\ strip_tac
  \\ gvs [sorted_desc_cons_not_mem]
QED

(* locals_rel *)

Triviality locals_rel_length:
  ∀xs ys zs.
    locals_rel xs ys zs ⇒ LENGTH xs = LENGTH ys ∧ LENGTH ys = LENGTH zs
Proof
  ho_match_mp_tac locals_rel_ind \\ gvs [locals_rel_def]
QED

Triviality locals_rel_drop:
  ∀n xs ys zs.
    locals_rel xs ys zs ⇒ locals_rel (DROP n xs) (DROP n ys) (DROP n zs)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ namedCases_on ‘xs’ ["", "x xs'"]
  \\ namedCases_on ‘ys’ ["", "y ys'"]
  \\ namedCases_on ‘zs’ ["", "z zs'"]
  \\ gvs [locals_rel_def]
  \\ PairCases_on ‘x’ \\ PairCases_on ‘y’ \\ PairCases_on ‘z’
  \\ gvs [locals_rel_def]
QED

Triviality locals_rel_append:
  ∀xs' ys' zs' xs ys zs.
    locals_rel xs' ys' zs' ∧
    locals_rel xs ys zs ⇒
    locals_rel (xs' ++ xs) (ys' ++ ys) (zs' ++ zs)
Proof
  recInduct locals_rel_ind \\ rpt strip_tac \\ gvs [locals_rel_def]
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

Triviality opt_mmap_read_local:
  ∀s t m m_old cnt ns vals.
    state_rel s t m m_old cnt ∧
    OPT_MMAP (read_local s.locals) ns = SOME vals ⇒
    OPT_MMAP (read_local t.locals) (MAP (lookup m) ns) = SOME vals
Proof
  ntac 5 gen_tac \\ Induct_on ‘ns’
  \\ gvs [OPT_MMAP_MAP_o, state_rel_def]
  \\ rpt strip_tac
  \\ drule_all locals_rel_read_local \\ rpt strip_tac \\ gvs []
QED

(* add_fresh *)

Triviality add_fresh_map_inv:
  add_fresh m cnt old = (cnt', m') ∧ map_inv m cnt ⇒
  map_inv m' cnt'
Proof
  rpt strip_tac \\ gvs [add_fresh_def]
  \\ gvs [map_inv_def]
  \\ drule every_less_weaken
  \\ disch_then $ qspec_then ‘cnt + 1’ assume_tac
  \\ gvs [greater_sorted_eq, EVERY_MEM]
QED

Triviality map_add_fresh_map_inv:
  ∀m cnt ns cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ∧ map_inv m cnt ⇒
    map_inv m' cnt'
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule add_fresh_map_inv \\ strip_tac \\ gvs []
  \\ last_x_assum drule \\ gvs []
QED

Triviality map_add_fresh_mono:
  ∀ns m m' cnt cnt'. map_add_fresh m cnt ns = (cnt', m') ⇒ cnt ≤ cnt'
Proof
  Induct
  \\ gvs [map_add_fresh_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ res_tac \\ gvs [add_fresh_def]
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

Triviality map_add_fresh_imp:
  map_add_fresh m₀ cnt ns = (cnt', m') ∧
  map_inv m₀ cnt ⇒
  ∃m₁.
    m' = m₁ ++ m₀ ∧ MAP FST m₁ = REVERSE ns ∧
    ALL_DISTINCT (MAP SND m₀ ++ MAP SND m₁)
Proof
  rpt strip_tac
  \\ drule map_add_fresh_map_inv
  \\ impl_tac >- (gvs [map_inv_def]) \\ strip_tac
  \\ drule map_add_fresh_exists \\ rpt strip_tac \\ gvs []
  \\ drule map_inv_distinct \\ strip_tac
  \\ gvs [ALL_DISTINCT_APPEND_COMM]
QED

Triviality map_add_fresh_all_distinct:
  ∀names m m' cnt cnt'.
    map_add_fresh m cnt names = (cnt', m') ∧
    map_inv m cnt ∧
    ALL_DISTINCT names ⇒
    ALL_DISTINCT (MAP (lookup m') names)
Proof
  rpt strip_tac
  \\ drule_all map_add_fresh_imp
  \\ rpt strip_tac \\ gvs [map_inv_def]
  \\ gvs [map_lookup_map_tostring]
  \\ gvs [ALL_DISTINCT_APPEND, MAP_REVERSE, distinct_nums_names]
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
  \\ dxrule locals_rel_append
  \\ disch_then dxrule \\ strip_tac
  \\ gvs [REVERSE_APPEND, MAP_REVERSE, REVERSE_ZIP]
  \\ drule_then assume_tac map_fst_reverse_imp
  \\ drule map_lookup_append_eq
  \\ disch_then $ qspec_then ‘m’ assume_tac \\ gvs []
QED

Triviality map_add_fresh_drop:
  ∀xs m m' cnt cnt'.
    map_add_fresh m cnt xs = (cnt', m') ⇒ m = DROP (LENGTH xs) m'
Proof
  Induct \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ qx_gen_tac ‘h’ \\ rpt strip_tac
  \\ drule map_add_fresh_exists
  \\ rpt strip_tac \\ gvs []
  \\ qabbrev_tac ‘ys = m₁ ++ [(h,cnt)]’
  \\ ‘SUC (LENGTH xs) = LENGTH ys’ by
    (unabbrev_all_tac \\ imp_res_tac REVERSE_LENGTH \\ gvs [ADD1])
  \\ simp []
  \\ DEP_REWRITE_TAC [DROP_LENGTH_APPEND]
QED

(* Monotonicity for freshen definitions *)

Triviality freshen_exp_mono:
  (∀m m_old cnt e cnt' e'.
     freshen_exp m m_old cnt e = (cnt', e') ⇒ cnt ≤ cnt') ∧
  (∀m m_old cnt es cnt' es'.
     freshen_exps m m_old cnt es = (cnt', es') ⇒ cnt ≤ cnt')
Proof
  ho_match_mp_tac freshen_exp_ind \\ rpt strip_tac
  \\ gvs [freshen_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [add_fresh_def]
  \\ imp_res_tac map_add_fresh_mono \\ simp []
QED

Triviality freshen_lhs_exp_mono:
 ∀m m_old cnt lhs cnt' lhs'.
    freshen_lhs_exp m m_old cnt lhs = (cnt', lhs') ⇒ cnt ≤ cnt'
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exp_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_exp_mono \\ gvs []
QED

Triviality freshen_lhs_exps_mono:
  ∀m m_old cnt lhss cnt' lhss'.
    freshen_lhs_exps m m_old cnt lhss = (cnt', lhss') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘lhss’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exps_def] \\ rpt (pairarg_tac \\ gvs[])
  \\ imp_res_tac freshen_lhs_exp_mono \\ res_tac \\ gvs []
QED

Triviality freshen_rhs_exp_mono:
 ∀m m_old cnt rhs cnt' rhs'.
    freshen_rhs_exp m m_old cnt rhs = (cnt', rhs') ⇒ cnt ≤ cnt'
Proof
  Cases_on ‘rhs’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exp_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_exp_mono \\ gvs []
QED

Triviality freshen_rhs_exps_mono:
  ∀m m_old cnt rhss cnt' rhss'.
    freshen_rhs_exps m m_old cnt rhss = (cnt', rhss') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘rhss’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exps_def] \\ rpt (pairarg_tac \\ gvs[])
  \\ imp_res_tac freshen_rhs_exp_mono \\ res_tac \\ gvs []
QED

Triviality freshen_stmt_mono:
  ∀m m_old cnt stmt cnt' stmt'.
    freshen_stmt m m_old cnt stmt = (cnt', stmt') ⇒ cnt ≤ cnt'
Proof
  Induct_on ‘stmt’ \\ rpt strip_tac
  \\ gvs [freshen_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ res_tac \\ imp_res_tac freshen_exp_mono
  \\ imp_res_tac freshen_rhs_exps_mono \\ imp_res_tac freshen_lhs_exps_mono
  \\ gvs [add_fresh_def]
QED

(* state_rel *)

Triviality state_rel_mono:
  state_rel s t m m_old cnt ∧ cnt ≤ cnt' ⇒ state_rel s t m m_old cnt'
Proof
  gvs [state_rel_def] \\ rpt strip_tac \\ imp_res_tac map_inv_mono
QED

Triviality state_rel_dec_clock:
  state_rel s t m m_old cnt ⇒
  state_rel (dec_clock s) (dec_clock t) m m_old cnt
Proof
  rpt strip_tac \\ gvs [state_rel_def, dec_clock_def]
QED

Triviality state_rel_same_map_imp:
  state_rel s t m m_old cnt ∧ state_rel s' t' m m_old cnt' ⇒
  state_rel s' t' m m_old cnt
Proof
  rpt strip_tac \\ gvs [state_rel_def]
QED

Triviality state_rel_push_locals:
  ∀names s t m m' m_old cnt cnt₂ cnt₃ vs.
    state_rel s t m m_old cnt ∧
    map_add_fresh m cnt₂ names = (cnt₃, m') ∧
    ALL_DISTINCT names ∧
    LENGTH vs = LENGTH names ∧
    cnt ≤ cnt₂ ⇒
    state_rel (push_locals s (ZIP (names,vs)))
      (push_locals t (ZIP (MAP (lookup m') names,vs))) m' m_old cnt₃
Proof
  Induct >-
   (rpt strip_tac
    \\ gvs [push_locals_def, map_add_fresh_def]
    \\ irule state_rel_mono
    \\ rpt (last_assum $ irule_at $ Pos last))
  \\ qx_gen_tac ‘name’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule add_fresh_map_inv
  \\ impl_tac >-
   (irule map_inv_mono
    \\ full_simp_tac std_ss [state_rel_def]
    \\ first_assum $ irule_at (Pos last)
    \\ simp [])
  \\ gvs [add_fresh_def]
  \\ namedCases_on ‘vs’ ["", "v vs'"] \\ gvs []
  \\ disch_tac
  \\ gvs [push_locals_cons]
  \\ last_x_assum irule \\ simp []
  \\ qexistsl [‘cnt₂ + 1’, ‘cnt₂ + 1’] \\ simp []
  \\ last_assum $ irule_at (Pos hd)
  \\ drule map_add_fresh_exists
  \\ disch_then $ qx_choose_then ‘m₁’ mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ DEP_REWRITE_TAC [not_mem_lookup_append_eq]
  \\ gvs [locals_rel_def, state_rel_def, push_local_def, lookup_def]
  \\ irule map_inv_mono
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Triviality state_rel_drop:
  state_rel s₁ t₁ m m_old cnt ∧
  state_rel s₂ t₂ m' m_old cnt₁ ∧
  map_add_fresh m cnt₂ names = (cnt₃,m') ∧
  n = LENGTH names ∧
  cnt ≤ cnt₁ ⇒
  state_rel (s₂ with locals := DROP n s₂.locals)
          (t₂ with locals := DROP n t₂.locals) m m_old cnt₁
Proof
  rpt strip_tac
  \\ gvs [state_rel_def]
  \\ conj_tac >- (* locals_rel *)
   (imp_res_tac map_add_fresh_drop \\ simp []
    \\ irule locals_rel_drop \\ simp [])
  \\ irule map_inv_mono
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

(* get_member *)

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

(* len_eq lemmas *)

Triviality freshen_exps_len_eq:
  ∀m m_old cnt es cnt' es'.
    freshen_exps m m_old cnt es = (cnt', es') ⇒ LENGTH es = LENGTH es'
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [freshen_exp_def] \\ rpt (pairarg_tac \\ gvs[]) \\ res_tac
QED

Triviality freshen_rhs_exp_len_eq:
  ∀m m_old cnt rhss cnt' rhss'.
    freshen_rhs_exps m m_old cnt rhss = (cnt', rhss') ⇒
    LENGTH rhss' = LENGTH rhss
Proof
  Induct_on ‘rhss’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ res_tac
QED

Triviality freshen_lhs_exp_len_eq:
  ∀m m_old cnt lhss cnt' lhss'.
    freshen_lhs_exps m m_old cnt lhss = (cnt', lhss') ⇒
    LENGTH lhss' = LENGTH lhss
Proof
  Induct_on ‘lhss’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ res_tac
QED

(* Proving the main theorems, namely the correctness of the freshen pass. *)

(* Used in the proof for function calls. *)
Triviality distinct_ins_lookup:
  map_add_fresh [] 0 ns = (cnt, m) ∧ ALL_DISTINCT ns ⇒
  ALL_DISTINCT (MAP (lookup m) ns)
Proof
  rpt strip_tac
  \\ drule map_add_fresh_imp \\ rpt strip_tac \\ gvs [map_inv_def]
  \\ gvs [map_lookup_map_tostring]
  \\ drule map_lookup_map_tostring
  \\ disch_then $ qspec_then ‘[]’ assume_tac \\ gvs []
  \\ gvs [MAP_REVERSE, distinct_nums_names]
QED

Theorem correct_freshen_exp:
  (∀s env e s' res t m m_old cnt cnt' e' env'.
     evaluate_exp s env e = (s', res) ∧ state_rel s t m m_old cnt ∧
     freshen_exp m m_old cnt e = (cnt', e') ∧
     env_rel env env' ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exp t env' e' = (t', res) ∧ state_rel s' t' m m_old cnt') ∧
  (∀s env es s' res t m m_old cnt cnt' es' env'.
     evaluate_exps s env es = (s', res) ∧ state_rel s t m m_old cnt ∧
     freshen_exps m m_old cnt es = (cnt', es') ∧
     env_rel env env' ∧ res ≠ Rerr Rtype_error ⇒
     ∃t'. evaluate_exps t env' es' = (t', res) ∧ state_rel s' t' m m_old cnt')
Proof
  ho_match_mp_tac evaluate_exp_ind \\ rpt strip_tac
  >~ [‘Let vars body’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘¬ALL_DISTINCT lhss’]
    \\ Cases_on ‘¬ALL_DISTINCT lhss’ \\ gvs []
    \\ drule map_add_fresh_all_distinct
    \\ impl_tac >-
     (gvs [UNZIP_MAP]
      \\ irule map_inv_mono
      \\ gvs [state_rel_def]
      \\ first_assum $ irule_at (Pos last)
      \\ imp_res_tac freshen_exp_mono)
    \\ disch_tac
    \\ rename [‘evaluate_exps _ _ rhss’]
    \\ namedCases_on ‘evaluate_exps s env rhss’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘ZIP (fresh_lhss, fresh_rhss)’
    \\ ‘LENGTH lhss = LENGTH rhss’ by (imp_res_tac UNZIP_LENGTH)
    \\ ‘LENGTH fresh_lhss = LENGTH fresh_rhss’ by
      (unabbrev_all_tac \\ imp_res_tac freshen_exps_len_eq \\ gvs [])
    \\ first_x_assum drule_all
    \\ disch_then $ qx_choose_then ‘t₁’ mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["vs", "err"] \\ gvs []
    >- (simp [evaluate_exp_def]
        \\ irule state_rel_mono
        \\ first_assum $ irule_at (Pos last)
        \\ imp_res_tac map_add_fresh_mono
        \\ imp_res_tac freshen_exp_mono \\ simp [])
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘evaluate_exp _ _ _ = (s₂,_)’]
    \\ imp_res_tac evaluate_exps_len_eq \\ gvs []
    \\ ‘LENGTH fresh_rhss ≤ LENGTH s₂.locals’ by
      (unabbrev_all_tac
       \\ imp_res_tac evaluate_exp_with_clock
       \\ gvs [push_locals_len])
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ last_x_assum $ drule_at (Pos last)
    \\ disch_then $ drule_at (Pos last)
    \\ disch_then $
         qspec_then ‘(push_locals t₁ (ZIP (fresh_lhss,vs)))’ mp_tac
    \\ impl_tac >-
     (unabbrev_all_tac
      \\ irule state_rel_push_locals \\ gvs []
      \\ first_assum $ irule_at $ Pos (el 2)
      \\ first_assum $ irule_at (Pos last) \\ simp [])
    \\ disch_then $ qx_choose_then ‘t₂’ mp_tac
    \\ rpt strip_tac
    \\ gvs [evaluate_exp_def]
    \\ ‘LENGTH t₂.locals = LENGTH s₂.locals’ by
      (gvs [state_rel_def] \\ imp_res_tac locals_rel_length \\ simp [])
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ irule state_rel_drop \\ gvs [PULL_EXISTS]
    \\ first_assum $ irule_at (Pos last)
    \\ first_assum $ irule_at (Pos last) \\ simp []
    \\ first_assum $ irule_at (Pos last)
    \\ imp_res_tac freshen_exp_mono
    \\ imp_res_tac map_add_fresh_mono
    \\ simp [])
  >~ [‘Old e’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp _ _ _ _ = (cnt₁, _)’]
    \\ gvs [evaluate_exp_def]
    \\ ‘env'.is_running = env.is_running’ by (gvs [env_rel_def]) \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exp (use_old s) env e’ ["s₁ r"] \\ gvs []
    \\ last_x_assum $ drule_at (Pos last)
    \\ disch_then $ drule_at (Pos last)
    \\ disch_then $ qspec_then ‘use_old t’ mp_tac
    \\ impl_tac >-
     (gvs [state_rel_def, use_old_def])
    \\ rpt strip_tac \\ simp []
    \\ gvs [state_rel_def, unuse_old_def]
    \\ irule map_inv_mono
    \\ last_assum $ irule_at (Pos last)
    \\ imp_res_tac freshen_exp_mono)
  >~ [‘FunCall name args’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exps _ _ _ _ = (cnt₁, args')’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ gvs []
    \\ drule_all get_member_some \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘member’ \\ gvs [freshen_member_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp _ _ _ body = (_, body')’,
               ‘map_add_fresh _ _ _ = (cnt₁, m')’]
    \\ namedCases_on ‘evaluate_exps s env args’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘state_rel s₁ t₁ _ _ cnt₁’]
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
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >-
     (gvs [restore_caller_def, state_rel_def])
    \\ gvs [CaseEq "prod"]
    \\ rename [‘evaluate_exp _ _ _ = (_, r)’]
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ qmatch_goalsub_abbrev_tac ‘evaluate_exp call_t’
    \\ disch_then $ qspec_then ‘call_t’ mp_tac
    \\ simp [Abbr ‘call_t’]
    \\ impl_tac
    >- (gvs [state_rel_def, dec_clock_def]
        \\ drule map_add_fresh_map_inv
        \\ impl_tac >- gvs [map_inv_def] \\ strip_tac
        \\ drule_all map_add_fresh_ins_locals_rel \\ strip_tac \\ gvs []
        \\ imp_res_tac freshen_exp_mono
        \\ imp_res_tac map_inv_mono)
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘state_rel s₃ t₃ m' m_old' _’]
    \\ Cases_on ‘r’ \\ gvs []
    \\ gvs [state_rel_def, restore_caller_def])
  >~ [‘Forall (v,ty) e’] >-
   (full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ qabbrev_tac ‘f = λval. evaluate_exp (push_local s v val) env e’
    \\ gvs [] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp m₁ _ cnt₁ e = (cnt₂,e₂)’]
    \\ full_simp_tac bool_ss [evaluate_exp_def, freshen_exp_def]
    \\ ‘state_rel s t m m_old cnt₂’ by
      (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono
       \\ gvs [add_fresh_def])
    \\ IF_CASES_TAC >- gvs [env_rel_def]
    \\ ‘t.clock = s.clock’ by gvs [state_rel_def]
    \\ IF_CASES_TAC >- gvs [env_rel_def]
    \\ qabbrev_tac ‘g = λval. evaluate_exp (push_local t (lookup m₁ v) val) env' e₂’
    \\ ‘s' = s’ by gvs [AllCaseEqs()]
    \\ gvs []
    \\ qexists_tac ‘t’ \\ gvs []
    \\ qpat_x_assum ‘_ = (s,res)’ mp_tac
    \\ IF_CASES_TAC >- gvs [env_rel_def] \\ rpt strip_tac
    \\ ‘∀v. v ∈ all_values ty ⇒ SND (f v) ≠ Rerr Rtype_error’ by
      (rpt strip_tac \\ qpat_x_assum ‘_ = (s,res)’ mp_tac
       \\ IF_CASES_TAC \\ gvs [])
    \\ qpat_x_assum ‘_ = (s,res)’ mp_tac
    \\ qsuff_tac ‘∀v. v ∈ all_values ty ⇒ SND (f v) = SND (g v)’ >-
     (rpt strip_tac \\ gvs [AllCaseEqs()] \\ metis_tac [])
    \\ unabbrev_all_tac \\ gvs []
    \\ qx_gen_tac ‘val’
    \\ strip_tac \\ last_x_assum drule \\ strip_tac
    \\ Cases_on ‘evaluate_exp (push_local s v val) env e’ \\ gvs []
    \\ last_x_assum $ qspec_then ‘val’ mp_tac \\ gvs []
    \\ disch_then $ drule_at $ Pos $ el 2
    \\ disch_then $ drule_at $ Pos $ el 2
    \\ disch_then $ qspec_then ‘(push_local t (lookup m₁ v) val)’ mp_tac
    \\ reverse impl_tac >- (strip_tac \\ gvs [])
    \\ gvs [state_rel_def]
    \\ drule_then assume_tac add_fresh_map_inv
    \\ gvs [state_rel_def, add_fresh_def,
            push_local_def, locals_rel_def, lookup_def]
    \\ irule map_inv_mono
    \\ last_assum $ irule_at (Pos last)
    \\ simp_tac std_ss [])
  >~ [‘Lit l’] >-
   (gvs [evaluate_exp_def, freshen_exp_def])
  >~ [‘Var v’] >-
   (gvs [evaluate_exp_def, freshen_exp_def, state_rel_def, CaseEq "option"]
    \\ imp_res_tac locals_rel_read_local)
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_mono
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env tst’ ["s₁ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac state_rel_mono
    \\ rename [‘evaluate_exp t env tst' = (t₁,Rval tst_v)’]
    \\ namedCases_on ‘do_cond tst_v thn els’ ["", "branch"] \\ gvs []
    \\ namedCases_on ‘do_cond tst_v thn' els'’ ["", "branch'"] \\ gvs []
    \\ gvs [oneline do_cond_def, AllCaseEqs ()]
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ disch_then $ drule_all \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac state_rel_mono)
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘do_uop uop v’ ["", "r"] \\ gvs [])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘freshen_exp m _ cnt e₀ = (cnt₁,e₀')’,
               ‘freshen_exp m _ cnt₁ e₁ = (cnt₂,e₁')’]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e₀’ ["s₁ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["v₀", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ rename [‘evaluate_exp t₁ env' e₁'’]
    \\ namedCases_on ‘do_sc bop v₀’ ["r", "", ""] \\ gvs []
    \\ imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono
    \\ namedCases_on ‘evaluate_exp s₁ env e₁’ ["s₂ r"] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["v₁", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘do_bop bop v₀ v₁’ ["", "r"] \\ gvs [])
  >~ [‘ArrLen arr’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"]
    \\ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs [])
  >~ [‘ArrSel arr idx’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ rename [‘evaluate_exp t _ _' = (t₁, _)’]
    \\ namedCases_on ‘evaluate_exp s₁ env idx’ ["s₂ r"]
    \\ namedCases_on ‘r’ ["idx_v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate_exp t₁ _ _' = (t₂, _)’]
    \\ namedCases_on ‘index_array s₂ arr_v idx_v’ ["", "v"] \\ gvs []
    \\ namedCases_on ‘index_array t₂ arr_v idx_v’ ["", "v'"] \\ gvs []
    \\ gvs [index_array_def, state_rel_def, AllCaseEqs ()])
  >~ [‘freshen_exps m m_old cnt []’] >- gvs [evaluate_exp_def, freshen_exp_def]
  >~ [‘freshen_exps m m_old cnt (e::es)’] >-
   (gvs [evaluate_exp_def, freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exps s₁ env es’ ["s₂ r"]
    \\ namedCases_on ‘r’ ["vs", "err"] \\ gvs []
    \\ first_x_assum $ drule_all \\ rpt strip_tac \\ gvs [])
QED

(* state_rel implies that updating the value of locals and the heap succeeds;
   it is also maintained. *)

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
  ∀s var rhs s' t m m_old cnt.
    update_local s var rhs = SOME s' ∧ state_rel s t m m_old cnt ⇒
    ∃t'.
      update_local t (lookup m var) rhs = SOME t' ∧
      state_rel s' t' m m_old cnt
Proof
  rpt strip_tac \\ gvs [update_local_def]
  \\ namedCases_on ‘update_local_aux s.locals var rhs’ ["", "slocals'"]
  \\ gvs [state_rel_def] \\ drule_all update_local_aux_locals_rel
  \\ rpt strip_tac \\ gvs []
QED

Triviality assign_value_state_rel:
  ∀s env lhs rhs s' res t m m_old cnt cnt' lhs' env'.
    assign_value s env lhs rhs = (s', res) ∧ state_rel s t m m_old cnt ∧
    freshen_lhs_exp m m_old cnt lhs = (cnt', lhs') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'.
      assign_value t env' lhs' rhs = (t', res) ∧ state_rel s' t' m m_old cnt'
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
  ∀s env lhss rhss s' res t m m_old cnt lhss' cnt' env'.
    assign_values s env lhss rhss = (s', res) ∧ state_rel s t m m_old cnt ∧
    freshen_lhs_exps m m_old cnt lhss = (cnt', lhss') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'.
      assign_values t env' lhss' rhss = (t', res) ∧ state_rel s' t' m m_old cnt'
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
  ∀s env rhs_e s' res t m m_old cnt cnt' rhs_e' env'.
    evaluate_rhs_exp s env rhs_e = (s', res) ∧ state_rel s t m m_old cnt ∧
    freshen_rhs_exp m m_old cnt rhs_e = (cnt', rhs_e') ∧ env_rel env env' ∧
    res ≠ Rerr Rtype_error ⇒
    ∃t'.
      evaluate_rhs_exp t env' rhs_e' = (t', res) ∧ state_rel s' t' m m_old cnt'
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
  ∀s env rhs_es s' res t m m_old cnt cnt' rhs_es' env'.
    evaluate_rhs_exps s env rhs_es = (s', res) ∧ state_rel s t m m_old cnt ∧
    freshen_rhs_exps m m_old cnt rhs_es = (cnt', rhs_es') ∧ env_rel env env' ∧
    res ≠ Rerr Rtype_error ⇒
    ∃t'.
      evaluate_rhs_exps t env' rhs_es' = (t', res) ∧
      state_rel s' t' m m_old cnt'
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

Triviality print_string_state_rel:
  print_string s v = SOME s' ∧ state_rel s t m m_old cnt ⇒
  ∃t'. print_string t v = SOME t' ∧ state_rel s' t' m m_old cnt
Proof
  rpt strip_tac
  \\ gvs [print_string_def, CaseEq "option", state_rel_def]
QED

(* Used in the proof for method calls. *)
Triviality distinct_ins_out_lookup:
  map_add_fresh [] 0 (MAP FST ins) = (cnt, m₀) ∧
  map_add_fresh m₀ cnt (MAP FST outs) = (cnt', m₁) ∧
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ⇒
  ALL_DISTINCT
    (MAP (lookup m₀) (MAP FST ins) ++ MAP (lookup m₁) (MAP FST outs))
Proof
  rpt strip_tac
  \\ rev_drule map_add_fresh_imp
  \\ impl_tac >- gvs [map_inv_def]
  \\ rpt strip_tac \\ gvs []
  \\ rev_drule map_add_fresh_map_inv
  \\ impl_tac >- gvs [map_inv_def]
  \\ rpt strip_tac \\ gvs []
  \\ drule map_add_fresh_imp \\ rpt strip_tac \\ gvs []
  \\ drule map_lookup_map_tostring \\ disch_then $ qspec_then ‘m₀’ mp_tac
  \\ impl_tac >- gvs [ALL_DISTINCT_APPEND] \\ strip_tac
  \\ rev_drule map_lookup_map_tostring \\ disch_then $ qspec_then ‘[]’ mp_tac
  \\ impl_tac >- gvs [ALL_DISTINCT_APPEND] \\ strip_tac
  \\ gvs [MAP_REVERSE, distinct_reverse_append, distinct_nums_names_append]
QED

Triviality IMP_LENGTH_EQ:
  xs = ys ⇒ LENGTH xs = LENGTH ys
Proof
  gvs []
QED

Triviality pop_local_some:
  s.locals ≠ [] ⇒ ∃s'. pop_locals 1 s = SOME s'
Proof
  rpt strip_tac \\ Cases_on ‘s.locals’ \\ gvs [safe_drop_def, pop_locals_def]
QED

Theorem correct_freshen_stmt:
  ∀s env stmt s' res t m m_old cnt cnt' stmt' env'.
    evaluate_stmt s env stmt = (s', res) ∧ state_rel s t m m_old cnt ∧
    freshen_stmt m m_old cnt stmt = (cnt', stmt') ∧ env_rel env env' ∧
    res ≠ Rstop (Serr Rtype_error) ⇒
    ∃t'. evaluate_stmt t env' stmt' = (t', res) ∧ state_rel s' t' m m_old cnt'
Proof
  ho_match_mp_tac evaluate_stmt_ind \\ rpt strip_tac
  >~ [‘MetCall lhss name args’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ rename [‘freshen_exps m _ cnt args = (cnt₁, args')’,
               ‘freshen_lhs_exps m _ cnt₁ lhss = (cnt₂, lhss')’]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ gvs []
    \\ drule_all get_member_some \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘member’ \\ gvs [freshen_member_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘map_add_fresh m₁' cnt₁' _ = (cnt₂', m₂')’,
               ‘freshen_stmt _ _ _ body = (_, body')’]
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
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >-
     (gvs [state_rel_def, restore_caller_def])
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
    \\ qmatch_goalsub_abbrev_tac ‘evaluate_stmt call_t’
    \\ disch_then $ qspec_then ‘call_t’ mp_tac
    \\ simp [Abbr ‘call_t’]
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
    >- gvs [restore_caller_def, state_rel_def]
    \\ rename [‘state_rel s₂ t₂ _ _ _’]
    \\ Cases_on ‘OPT_MMAP (read_local s₂.locals) (MAP FST outs)’ \\ gvs []
    \\ drule_all opt_mmap_read_local \\ strip_tac \\ gvs []
    \\ rename [‘OPT_MMAP _ _ = SOME out_vs’]
    \\ gvs [restore_caller_def]
    \\ ‘LENGTH lhss' = LENGTH lhss’ by (imp_res_tac freshen_lhs_exp_len_eq)
    \\ IF_CASES_TAC \\ gvs []
    \\ qmatch_asmsub_abbrev_tac ‘assign_values s₂_with’
    \\ namedCases_on ‘assign_values s₂_with env lhss out_vs’ ["st₃ r"]
    \\ simp [Abbr ‘s₂_with’]
    \\ Cases_on ‘r = Rstop (Serr Rtype_error)’ \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘assign_values t₂_with’
    \\ drule assign_values_state_rel \\ gvs []
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $ qspec_then ‘t₂_with’ mp_tac
    \\ simp [Abbr ‘t₂_with’]
    \\ impl_tac >- (gvs [state_rel_def])
    \\ rpt strip_tac \\ gvs []
    \\ gvs [AllCaseEqs(), state_rel_def])
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘add_fresh m cnt old = (cnt₁, m')’]
    \\ qabbrev_tac ‘s₁ = declare_local s old’
    \\ rename [‘freshen_stmt m' _ cnt₁ scope = (cnt₂, scope')’,
               ‘evaluate_stmt s₁ env scope = (s₂, r)’]
    \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ qabbrev_tac ‘t₁ = declare_local t (lookup m' old)’
    \\ rename [‘evaluate_stmt t₁ _ _' = (t₂, r')’]
    \\ imp_res_tac evaluate_stmt_locals \\ gvs []
    \\ ‘s₂.locals ≠ []’ by
      (spose_not_then assume_tac \\ gvs [declare_local_def]
       \\ unabbrev_all_tac \\ imp_res_tac IMP_LENGTH_EQ \\ gvs [])
    \\ ‘t₂.locals ≠ []’ by
      (spose_not_then assume_tac \\ gvs [declare_local_def]
       \\ unabbrev_all_tac \\ imp_res_tac IMP_LENGTH_EQ \\ gvs [])
    \\ imp_res_tac pop_local_some
    \\ rename [‘pop_locals _ _ = SOME s₃’] \\ pop_assum $ mp_tac
    \\ rename [‘pop_locals _ _ = SOME t₃’] \\ strip_tac
    \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (spose_not_then assume_tac \\ gvs [])
    \\ qsuff_tac ‘state_rel s₁ t₁ m' m_old cnt₁’
    >- (strip_tac \\ last_x_assum $ drule_all \\ strip_tac \\ gvs []
        \\ rename [‘evaluate_stmt _ _ _' = (t₂, _)’]
        \\ gvs [state_rel_def, pop_locals_def, safe_drop_def, add_fresh_def,
                AllCaseEqs()]
        \\ Cases_on ‘s₂.locals’ \\ gvs []
        \\ Cases_on ‘t₂.locals’ \\ gvs []
        \\ imp_res_tac locals_rel_pop
        \\ drule map_inv_pop \\ gvs [])
    \\ unabbrev_all_tac
    \\ gvs [state_rel_def]
    \\ drule_then assume_tac add_fresh_map_inv
    \\ gvs [declare_local_def, add_fresh_def]
    \\ imp_res_tac locals_rel_push \\ gvs []
    \\ irule map_inv_mono
    \\ first_assum $ irule_at (Pos last) \\ simp [])
  >~ [‘Then stmt₀ stmt₁’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_stmt s env stmt₀’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    \\ last_x_assum drule_all \\ gvs []
    \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_stmt_mono \\ imp_res_tac state_rel_mono)
    \\ last_x_assum drule \\ gvs [])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ rename [‘freshen_exp m _ cnt tst = (cnt₁, tst')’]
    \\ pop_assum $ mp_tac \\ rename [‘freshen_stmt _ _ _ _ = (cnt₂, thn')’]
    \\ disch_then assume_tac \\ rename [‘freshen_stmt _ _ _ _ = (cnt₃, els')’]
    \\ imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono
    \\ ‘state_rel s t m m_old cnt₁’ by (imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exp s env tst’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    \\ rename [‘evaluate_exp _ _ _ = (s₁, _)’]
    \\ drule (cj 1 correct_freshen_exp) \\ gvs []
    \\ disch_then drule_all \\ rpt strip_tac \\ gvs []
    >- imp_res_tac state_rel_mono
    \\ rename [‘evaluate_exp _ _ _ = (t₁,_)’]
    \\ gvs [oneline do_cond_def, AllCaseEqs ()]
    >- (last_x_assum drule_all \\ rpt strip_tac \\ gvs []
        \\ imp_res_tac state_rel_mono)
    \\ ‘state_rel s₁ t₁ m m_old cnt₂’ by imp_res_tac state_rel_mono
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs [])
  >~ [‘Assign ass’] >-
   (gvs [evaluate_stmt_def]
    \\ qabbrev_tac ‘rhss = (MAP SND ass)’
    \\ qabbrev_tac ‘lhss = (MAP FST ass)’
    \\ ‘LENGTH rhss = LENGTH lhss’ by (unabbrev_all_tac \\ gvs [])
    \\ gvs [freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ drule_then assume_tac freshen_rhs_exp_len_eq
    \\ drule_then assume_tac freshen_lhs_exp_len_eq
    \\ gvs [MAP_ZIP]
    \\ namedCases_on ‘evaluate_rhs_exps s env rhss’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["rhss_v", "err"] \\ gvs []
    \\ rename [‘evaluate_rhs_exps _ _ _ = (s₁, _)’]
    \\ qspecl_then [‘s’, ‘env’, ‘rhss’, ‘s₁’] mp_tac correct_freshen_rhs_exps
    \\ gvs [] \\ disch_then drule_all \\ rpt strip_tac \\ gvs []
    >- (imp_res_tac freshen_lhs_exps_mono \\ imp_res_tac state_rel_mono)
    \\ rename [‘assign_values s₁ env lhss rhss_v = (s₂,res)’]
    \\ irule assign_values_state_rel \\ gvs []
    \\ gvs [SF SFY_ss])
  >~ [‘While grd invs decrs mods body’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ ‘t.clock = s.clock’ by gvs [state_rel_def] \\ gvs []
    \\ Cases_on ‘s.clock = 0’ \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono
        \\ imp_res_tac state_rel_mono \\ gvs [])
    \\ namedCases_on ‘evaluate_exp (dec_clock s) env grd’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule (cj 1 correct_freshen_exp) \\ gvs []
    \\ ntac 2 (disch_then $ drule_at (Pos last))
    \\ disch_then $ qspec_then ‘dec_clock t’ mp_tac
    \\ impl_tac >- (irule state_rel_dec_clock \\ gvs [])
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate_exp t env' grd' = (t₁, _)’]
    \\ reverse $ namedCases_on ‘r’ ["grd_v", "err"] \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono
        \\ imp_res_tac state_rel_mono \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac freshen_stmt_mono
        \\ imp_res_tac state_rel_mono \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_stmt s₁ env body’ ["s₂ r"] \\ gvs []
    \\ rename [‘freshen_stmt m _ cnt₅ body = (cnt', body')’]
    \\ ‘state_rel s₁ t₁ m m_old cnt₅’ by
         (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    \\ disch_then drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate_stmt _ _ _ = (t₂,_)’]
    \\ gvs [STOP_def]
    \\ rev_drule state_rel_same_map_imp \\ disch_then dxrule \\ strip_tac
    \\ last_x_assum drule
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $
         qspecl_then [‘cnt'’, ‘While grd' invs' decrs' mods' body'’] mp_tac
    \\ impl_tac >- gvs [freshen_stmt_def]
    \\ rpt strip_tac \\ gvs [])
  >~ [‘Print e ty’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (Cases_on ‘r’ \\ gvs [])
    \\ drule_all (cj 1 correct_freshen_exp) \\ gvs []
    \\ disch_then $ qx_choose_then ‘t₁’ assume_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ namedCases_on ‘print_string s₁ v’ ["", "s₂"] \\ gvs []
    \\ drule_all print_string_state_rel \\ rpt strip_tac \\ gvs [])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def, freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [evaluate_stmt_def]
    \\ ‘env'.is_running = env.is_running’ by gvs [env_rel_def] \\ gvs []
    \\ Cases_on ‘env.is_running’ \\ gvs []
    >- (imp_res_tac freshen_exp_mono \\ imp_res_tac state_rel_mono)
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r"] \\ gvs []
    \\ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ drule (cj 1 correct_freshen_exp) \\ gvs [] \\ disch_then drule_all
    \\ rpt strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  \\ gvs [evaluate_stmt_def, freshen_stmt_def]
QED

Triviality MAP_member_name_MAP_freshen_member_eq:
  ∀members.
    (MAP member_name (MAP freshen_member members)) =
    (MAP member_name members)
Proof
  Induct \\ simp []
  \\ Cases \\ simp [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality locals_rel_nil_eq:
  locals_rel xs [] ys ⇒ xs = [] ∧ ys = []
Proof
  rpt strip_tac
  \\ namedCases_on ‘xs’ ["", "x xs"]
  \\ namedCases_on ‘ys’ ["", "y ys"]
  \\ gvs [locals_rel_def]
QED

(* Correctness of the freshen pass. *)
Theorem correct_freshen_program:
  ∀ck is_running prog s r.
    evaluate_program ck is_running prog = (s, r) ∧
    r ≠ Rstop (Serr Rtype_error) ⇒
    evaluate_program ck is_running (freshen_program prog) = (s, r)
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [evaluate_program_def, freshen_program_def,
          MAP_member_name_MAP_freshen_member_eq]
  \\ IF_CASES_TAC \\ gvs []
  \\ ‘state_rel (init_state ck) (init_state ck) [] [] 0’ by
       gvs [state_rel_def, init_state_def, locals_rel_def, map_inv_def]
  \\ ‘freshen_stmt [] [] 0 (MetCall [] «Main» []) = (0, MetCall [] «Main» [])’ by
       gvs [freshen_stmt_def, freshen_lhs_exps_def, freshen_exp_def]
  \\ ‘env_rel
        (mk_env is_running (Program members))
        (mk_env is_running (Program (MAP freshen_member members)))’ by
    (gvs [freshen_program_def, env_rel_def, mk_env_def])
  \\ drule_all correct_freshen_stmt
  \\ rpt strip_tac \\ gvs []
  \\ imp_res_tac evaluate_stmt_locals
  \\ gvs [state_rel_def, init_state_def, state_component_equality]
  \\ imp_res_tac locals_rel_nil_eq \\ simp []
QED

(** is_fresh: After the freshening pass, all variable names start with v. **)
(* Returns whether the name comes from the freshen pass. *)
Definition is_fresh_def:
  is_fresh name = isPrefix «v» name
End

Triviality list_size_snd:
  list_size (λx. exp_size (SND x)) vars =
  list_size (λx. exp_size x) (MAP SND vars)
Proof
  Induct_on ‘vars’ \\ gvs []
QED

(* NOTE If we have multiple of these, can abstract aways into a function that
   takes a predicate, and walks the AST *)
Definition is_fresh_exp_def[simp]:
  (is_fresh_exp (Lit _) ⇔ T) ∧
  (is_fresh_exp (Var name) ⇔ is_fresh name) ∧
  (is_fresh_exp (If tst thn els) ⇔
     is_fresh_exp tst ∧ is_fresh_exp thn ∧ is_fresh_exp els) ∧
  (is_fresh_exp (UnOp _ e) ⇔ is_fresh_exp e) ∧
  (is_fresh_exp (BinOp _ e₀ e₁) ⇔
     is_fresh_exp e₀ ∧ is_fresh_exp e₁) ∧
  (is_fresh_exp (ArrLen arr) ⇔ is_fresh_exp arr) ∧
  (is_fresh_exp (ArrSel arr idx) ⇔
     is_fresh_exp arr ∧ is_fresh_exp idx) ∧
  (is_fresh_exp (FunCall name es) ⇔
     EVERY (λe. is_fresh_exp e) es) ∧
  (is_fresh_exp (Forall (name, _) term) ⇔
     is_fresh name ∧ is_fresh_exp term) ∧
  (is_fresh_exp (Old e) ⇔ is_fresh_exp e) ∧
  (is_fresh_exp (Let vars body) ⇔
     EVERY (λn. is_fresh n) (MAP FST vars) ∧
     EVERY (λe. is_fresh_exp e) (MAP SND vars) ∧
     is_fresh_exp body)
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Definition is_fresh_lhs_exp[simp]:
  (is_fresh_lhs_exp (VarLhs name) ⇔ is_fresh name) ∧
  (is_fresh_lhs_exp (ArrSelLhs arr idx) ⇔
     is_fresh_exp arr ∧ is_fresh_exp idx)
End

Definition is_fresh_rhs_exp[simp]:
  (is_fresh_rhs_exp (ExpRhs e) ⇔ is_fresh_exp e) ∧
  (is_fresh_rhs_exp (ArrAlloc len init_e) ⇔
     is_fresh_exp len ∧ is_fresh_exp init_e)
End

Definition is_fresh_stmt_def[simp]:
  (is_fresh_stmt Skip ⇔ T) ∧
  (is_fresh_stmt (Assert e) ⇔ is_fresh_exp e) ∧
  (is_fresh_stmt (Then stmt₀ stmt₁) ⇔
     is_fresh_stmt stmt₀ ∧ is_fresh_stmt stmt₁) ∧
  (is_fresh_stmt (If cnd thn els) ⇔
     is_fresh_exp cnd ∧ is_fresh_stmt thn ∧ is_fresh_stmt els) ∧
  (is_fresh_stmt (Dec (n, _) scope) ⇔
     is_fresh n ∧ is_fresh_stmt scope) ∧
  (is_fresh_stmt (Assign ass) ⇔
     EVERY (λlhs. is_fresh_lhs_exp lhs) (MAP FST ass) ∧
     EVERY (λrhs. is_fresh_rhs_exp rhs) (MAP SND ass)) ∧
  (is_fresh_stmt (While grd invs decrs mods body) ⇔
     is_fresh_exp grd ∧
     EVERY (λe. is_fresh_exp e) invs ∧
     EVERY (λe. is_fresh_exp e) decrs ∧
     EVERY (λe. is_fresh_exp e) mods ∧
     is_fresh_stmt body) ∧
  (is_fresh_stmt (Print e _) ⇔ is_fresh_exp e) ∧
  (is_fresh_stmt (MetCall lhss _ args) ⇔
     EVERY (λlhs. is_fresh_lhs_exp lhs) lhss ∧
     EVERY (λe. is_fresh_exp e) args) ∧
  (is_fresh_stmt Return ⇔ T)
End

Definition is_fresh_member_def[simp]:
  (is_fresh_member (Method _ ins reqs ens rds decrs outs mods body) ⇔
     EVERY (λn. is_fresh n) (MAP FST ins) ∧
     EVERY (λe. is_fresh_exp e) reqs ∧
     EVERY (λe. is_fresh_exp e) ens ∧
     EVERY (λe. is_fresh_exp e) rds ∧
     EVERY (λe. is_fresh_exp e) decrs ∧
     EVERY (λn. is_fresh n) (MAP FST outs) ∧
     is_fresh_stmt body) ∧
  (is_fresh_member (Function _ ins _ reqs rds decrs body) ⇔
     EVERY (λn. is_fresh n) (MAP FST ins) ∧
     EVERY (λe. is_fresh_exp e) reqs ∧ EVERY (λe. is_fresh_exp e) rds ∧
     EVERY (λe. is_fresh_exp e) decrs ∧ is_fresh_exp body)
End

Triviality add_fresh_is_fresh:
  add_fresh m cnt v = (cnt', m') ⇒ is_fresh (lookup m' v)
Proof
  disch_tac \\ gvs [add_fresh_def, lookup_def, is_fresh_def, isprefix_strcat]
QED

Triviality map_add_fresh_every_is_fresh:
  ∀ns m cnt cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ⇒
    EVERY (λn. is_fresh n) (MAP (lookup m') ns)
Proof
  Induct \\ simp []
  \\ qx_gen_tac ‘n’ \\ rpt strip_tac
  >-
   (drule map_add_fresh_exists
    \\ rpt strip_tac \\ gvs []
    \\ ‘MEM n (MAP FST m₁)’ by gvs []
    \\ drule lookup_append_eq \\ simp []
    \\ disch_then kall_tac
    \\ simp [lookup_def]
    \\ CASE_TAC
    >- (gvs [ALOOKUP_NONE])
    \\ simp [is_fresh_def, isprefix_strcat])
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ last_assum irule
  \\ last_assum $ irule_at Any
QED

Triviality freshen_exp_is_fresh:
  (∀m m_old cnt e cnt' e'.
     freshen_exp m m_old cnt e = (cnt', e') ⇒ is_fresh_exp e') ∧
  (∀m m_old cnt es cnt' es'.
     freshen_exps m m_old cnt es = (cnt', es') ⇒
     EVERY (λe. is_fresh_exp e) es')
Proof
  ho_match_mp_tac freshen_exp_ind
  \\ rpt strip_tac
  >~ [‘Let vars body’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [is_fresh_exp_def]
    \\ imp_res_tac freshen_exps_len_eq
    \\ gvs [GSYM MAP_MAP_o, MAP_ZIP, UNZIP_MAP]
    \\ irule map_add_fresh_every_is_fresh
    \\ first_assum $ irule_at (Pos hd))
  >~ [‘Var v’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [is_fresh_def, lookup_def]
    \\ CASE_TAC >- (simp [isprefix_thm])
    \\ simp [isprefix_strcat])
  >~ [‘Forall (v,ty) e’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac add_fresh_is_fresh)
  \\ gvs [freshen_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality freshen_lhs_exp_is_fresh:
  freshen_lhs_exp m m_old cnt lhs = (cnt', lhs') ⇒ is_fresh_lhs_exp lhs'
Proof
  Cases_on ‘lhs’
  >~ [‘VarLhs var’] >-
   (rpt strip_tac
    \\ gvs [is_fresh_lhs_exp, freshen_lhs_exp_def, lookup_def, is_fresh_def]
    \\ CASE_TAC >- simp [isprefix_thm]
    \\ simp [isprefix_strcat])
  >~ [‘ArrSelLhs arr idx’] >-
   (rpt strip_tac
    \\ gvs [freshen_lhs_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp [])
QED

Triviality freshen_lhs_exps_is_fresh:
  ∀lhss m m_old cnt cnt' lhss'.
    freshen_lhs_exps m m_old cnt lhss = (cnt', lhss') ⇒
    EVERY (λe. is_fresh_lhs_exp e) lhss'
Proof
  Induct \\ simp [freshen_lhs_exps_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_lhs_exp_is_fresh \\ simp []
  \\ res_tac
QED

Triviality freshen_rhs_exp_is_fresh:
  freshen_rhs_exp m m_old cnt rhs = (cnt', rhs') ⇒ is_fresh_rhs_exp rhs'
Proof
  Cases_on ‘rhs’
  >~ [‘ExpRhs e’] >-
   (simp [freshen_rhs_exp_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh))
  >~ [‘ArrAlloc len init’] >-
   (simp [freshen_rhs_exp_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp [])
QED

Triviality freshen_rhs_exps_is_fresh:
  ∀rhss m m_old cnt cnt' rhss'.
    freshen_rhs_exps m m_old cnt rhss = (cnt', rhss') ⇒
    EVERY (λe. is_fresh_rhs_exp e) rhss'
Proof
  Induct \\ simp [freshen_rhs_exps_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_rhs_exp_is_fresh \\ simp []
  \\ res_tac
QED

Triviality freshen_stmt_is_fresh:
  ∀stmt m m_old cnt cnt' stmt'.
    freshen_stmt m m_old cnt stmt = (cnt', stmt') ⇒ is_fresh_stmt stmt'
Proof
  Induct \\ rpt gen_tac
  >~ [‘MetCall lhss name args’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_lhs_exps_is_fresh \\ simp []
    \\ imp_res_tac (cj 2 freshen_exp_is_fresh))
  >~ [‘Dec local scope’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac add_fresh_is_fresh \\ simp []
    \\ res_tac)
  >~ [‘Then stmt₀ stmt₁’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ res_tac \\ simp [])
  >~ [‘If tst thn els’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp []
    \\ res_tac \\ simp [])
  >~ [‘Assign ass’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ EVERY (map imp_res_tac
               [freshen_rhs_exp_len_eq, freshen_lhs_exp_len_eq,
                freshen_rhs_exps_is_fresh, freshen_lhs_exps_is_fresh])
    \\ simp [MAP_ZIP])
  >~ [‘While grd invs decrs mods body’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_is_fresh
    \\ simp [] \\ res_tac)
  >~ [‘Print e ty’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_is_fresh)
  >~ [‘Assert e’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_is_fresh)
  (* Return, Skip *)
  \\ simp [freshen_stmt_def]
QED

Theorem freshen_member_is_fresh:
  ALL_DISTINCT (get_param_names member) ⇒
  is_fresh_member (freshen_member member)
Proof
  disch_tac
  \\ namedCases_on ‘member’
       ["name ins reqs ens rds decrs outs mods body",
        "name ins res_t reqs rds decrs body"]
  \\ gvs [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ EVERY (map imp_res_tac
                [freshen_exp_is_fresh, UNZIP_LENGTH,
                 map_add_fresh_every_is_fresh, freshen_stmt_is_fresh])
  \\ gvs [MAP_ZIP, UNZIP_MAP, ALL_DISTINCT_APPEND]
QED

(** no_shadow: After the freshening pass no variables are shadowed. **)

Definition no_shadow_def[simp]:
  (no_shadow t (Dec (n, _) scope) ⇔
     n ∉ t ∧ no_shadow (n INSERT t) scope) ∧
  (no_shadow t (Then stmt₁ stmt₂) ⇔
     no_shadow t stmt₁ ∧ no_shadow t stmt₂) ∧
  (no_shadow t (If _ thn els) ⇔
     no_shadow t thn ∧ no_shadow t els) ∧
  (no_shadow t (While _ _ _ _ body) ⇔
     no_shadow t body) ∧
  (no_shadow _ _ ⇔ T)
End

Definition no_shadow_method_def[simp]:
  no_shadow_method (Method _ ins _ _ _ _ out _ body) =
    no_shadow (set ((MAP FST ins) ++ (MAP FST out))) body ∧
  no_shadow_method _ = T
End

Triviality freshen_stmt_no_shadow:
  ∀stmt m cnt cnt' stmt'.
    freshen_stmt m m_old cnt stmt = (cnt', stmt') ∧
    map_inv m cnt ⇒
    no_shadow (set (MAP (λi. «v» ^ toString i) (MAP SND m))) stmt'
Proof
  Induct \\ rpt gen_tac
  >~ [‘Dec local scope’] >-
   (rpt strip_tac
    \\ gvs [freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ drule_all add_fresh_map_inv \\ disch_tac
    \\ gvs [add_fresh_def, lookup_def]
    \\ conj_tac >-
     (simp [MEM_MAP] \\ rpt strip_tac
      \\ gvs [num_to_str_11]
      \\ rename [‘MEM y m’]
      \\ gvs [map_inv_def, EVERY_MEM]
      \\ last_assum $ qspec_then ‘SND y’ mp_tac
      \\ simp [MEM_MAP]
      \\ last_assum $ irule_at (Pos last) \\ simp [])
    \\ last_x_assum drule \\ gvs [] \\ disch_tac)
  >~ [‘Then stmt₀ stmt₁’] >-
   (rpt strip_tac
    \\ gvs [freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ last_x_assum $ irule_at (Pos hd)
    \\ last_assum $ irule_at (Pos hd) \\ simp []
    \\ last_x_assum $ irule
    \\ last_assum $ irule_at (Pos hd)
    \\ irule map_inv_mono
    \\ last_assum $ irule_at (Pos last)
    \\ imp_res_tac freshen_stmt_mono)
  >~ [‘If tst thn els’] >-
   (rpt strip_tac
    \\ gvs [freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ last_x_assum $ irule_at (Pos hd)
    \\ last_assum $ irule_at (Pos hd)
    \\ irule_at (Pos hd) map_inv_mono
    \\ last_assum $ irule_at (Pos hd)
    \\ imp_res_tac freshen_exp_mono \\ simp []
    \\ last_x_assum irule
    \\ first_assum $ irule_at (Pos hd)
    \\ irule map_inv_mono
    \\ last_assum $ irule_at (Pos last)
    \\ imp_res_tac freshen_stmt_mono \\ simp [])
  >~ [‘While grd invs decrs mods body’] >-
   (rpt strip_tac
    \\ gvs [freshen_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ last_x_assum irule
    \\ first_assum $ irule_at (Pos hd)
    \\ irule map_inv_mono
    \\ last_assum $ irule_at (Pos last)
    \\ imp_res_tac freshen_exp_mono
    \\ imp_res_tac freshen_stmt_mono \\ simp [])
  \\ rpt strip_tac
  \\ gvs [freshen_stmt_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem no_shadow_method_freshen_member:
  ALL_DISTINCT (get_param_names member) ⇒
  no_shadow_method (freshen_member member)
Proof
  disch_tac
  \\ namedCases_on ‘member’
       ["name ins reqs ens rds decrs outs mods body",
        "name ins res_t reqs rds decrs body"]
  \\ simp [freshen_member_def]
  \\ rpt (pairarg_tac \\ simp [])
  \\ imp_res_tac UNZIP_LENGTH
  \\ gvs [MAP_ZIP, UNZIP_MAP]
  \\ rev_drule map_add_fresh_map_inv
  \\ impl_tac >- (gvs [map_inv_def])
  \\ disch_tac
  \\ drule map_add_fresh_map_inv
  \\ simp []
  \\ disch_tac
  \\ drule freshen_stmt_no_shadow
  \\ impl_tac >-
   (EVERY
    (map imp_res_tac [cj 2 freshen_exp_mono, freshen_stmt_mono, map_inv_mono]))
  \\ rpt strip_tac
  \\ drule map_add_fresh_exists
  \\ rpt strip_tac \\ gvs []
  \\ drule map_lookup_append_eq \\ simp []
  \\ disch_then kall_tac
  \\ rev_drule map_add_fresh_exists
  \\ rpt strip_tac \\ gvs []
  \\ ‘MAP FST ins = REVERSE (MAP FST m)’ by (gvs []) \\ fs []
  \\ ‘MAP FST outs = REVERSE (MAP FST m₁)’ by (gvs []) \\ fs []
  \\ simp [MAP_REVERSE]
  \\ DEP_REWRITE_TAC [gen_map_lookup_map_tostring]
  \\ conj_tac >- (gvs [ALL_DISTINCT_APPEND])
  \\ gvs [UNION_COMM]
QED
