open preamble;
open rich_listTheory listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory typeSysPropsTheory;
open miscLib BasicProvers

local open evalPropsTheory typeSoundInvariantsTheory in
val check_dup_ctors_cons = check_dup_ctors_cons;
val tenvT_ok_def = tenvT_ok_def;
val flat_tenvT_ok_def = flat_tenvT_ok_def;
end;

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
srw_tac[] [fmap_EXT]);


val _ = new_theory "inferProps";

val fevery_to_drestrict = Q.prove (
`!P m s.
  FEVERY P m ⇒ FEVERY P (DRESTRICT m s)`,
 srw_tac[] [FEVERY_ALL_FLOOKUP,FLOOKUP_DRESTRICT]);

(* Not sure these are general enough to go elsewhere.*)
val flookup_update_list_none = Q.store_thm ("flookup_update_list_none",
`!x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (ALOOKUP l x = NONE))`,
 srw_tac[] [flookup_fupdate_list] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss()) [] >>
 metis_tac []);

val flookup_update_list_some = Q.store_thm ("flookup_update_list_some",
`!x m l y. 
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((ALOOKUP (REVERSE l) x = SOME y) ∨
   ((ALOOKUP l x = NONE) ∧ (FLOOKUP m x = SOME y)))`,
 srw_tac[] [flookup_fupdate_list] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss()) [] >>
 metis_tac []);

val every_shim2 = Q.prove (
`!l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)`,
induct_on `l` >>
srw_tac[] [] >>
PairCases_on `h` >>
srw_tac[] [] >>
metis_tac []);

val every_shim = Q.store_thm ("every_shim",
`!l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)`,
induct_on `l` >>
srw_tac[] [] >>
PairCases_on `h` >>
srw_tac[] []);

(* ---------- Facts about deBruijn increment ---------- *)

val infer_deBruijn_inc0 = Q.store_thm ("infer_deBruijn_inc0",
`!(n:num) t. infer_deBruijn_inc 0 t = t`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
srw_tac[] [infer_deBruijn_inc_def] >>
induct_on `ts` >>
srw_tac[] []);

val infer_deBruijn_inc0_id = Q.store_thm ("infer_deBruijn_inc0_id",
`infer_deBruijn_inc 0 = (\x.x)`,
metis_tac [infer_deBruijn_inc0]);

val t_vars_inc = Q.store_thm ("t_vars_inc",
`!tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
srw_tac[] [t_vars_def, encode_infer_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
srw_tac[] [encode_infer_t_def]);

val inc_wfs = Q.store_thm ("inc_wfs",
`!tvs s. t_wfs s ⇒ t_wfs (infer_deBruijn_inc tvs o_f s)`,
srw_tac[] [t_wfs_eqn] >>
`t_vR s = t_vR (infer_deBruijn_inc tvs o_f s)`
       by (srw_tac[] [FLOOKUP_o_f, FUN_EQ_THM, t_vR_eqn] >>
           full_case_tac  >>
           srw_tac[] [t_vars_inc]) >>
metis_tac []);

val vwalk_inc = Q.store_thm ("vwalk_inc",
`!s tvs n.
  t_wfs s
  ⇒
  t_vwalk (infer_deBruijn_inc tvs o_f s) n = infer_deBruijn_inc tvs (t_vwalk s n)`,
srw_tac[] [] >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
srw_tac[] [] >>
Q.SPEC_TAC (`n`, `n`) >>
qpat_assum `!p. (!v. q v ⇒ p v) ⇒ !v. p v` ho_match_mp_tac >>
srw_tac[] [] >>
imp_res_tac t_vwalk_eqn >>
once_asm_rewrite_tac [] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
cases_on `FLOOKUP s n` >>
srw_tac[] [FLOOKUP_o_f, infer_deBruijn_inc_def] >>
cases_on `x` >>
srw_tac[] [infer_deBruijn_inc_def]);

val walk_inc = Q.store_thm ("walk_inc",
`!s tvs t.
  t_wfs s
  ⇒
  t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) = infer_deBruijn_inc tvs (t_walk s t)`,
srw_tac[] [] >>
cases_on `t` >>
srw_tac[] [t_walk_eqn, infer_deBruijn_inc_def, vwalk_inc]);

val walkstar_inc = Q.store_thm ("walkstar_inc",
`!tvs s t.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) =
   infer_deBruijn_inc tvs (t_walkstar s t))`,
srw_tac[] [] >>
imp_res_tac t_walkstar_ind >>
Q.SPEC_TAC (`t`, `t`) >>
pop_assum ho_match_mp_tac >>
srw_tac[] [] >>
srw_tac[] [walk_inc] >>
cases_on `t_walk s t` >>
srw_tac[] [infer_deBruijn_inc_def] >>
imp_res_tac inc_wfs >>
srw_tac[] [t_walkstar_eqn,infer_deBruijn_inc_def, walk_inc] >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum (fn _ => all_tac) >>
induct_on `l` >>
srw_tac[] [] >>
full_simp_tac(srw_ss()) []);

val walkstar_inc2 = Q.store_thm ("walkstar_inc2",
`!tvs s n.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
   infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))`,
srw_tac[] [GSYM walkstar_inc, infer_deBruijn_inc_def]);

(* ---------- Type substitution ---------- *)

val subst_infer_subst_swap = Q.store_thm ("subst_infer_subst_swap",
`(!t tvs s uvar.
  t_wfs s ⇒
  (t_walkstar s (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))) t)
   =
   infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs)))) t)) ∧
 (!ts tvs s uvar.
  t_wfs s ⇒
  (MAP (t_walkstar s) (MAP (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs))))) ts)
   =
   MAP (infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs))))) ts))`, 
 ho_match_mp_tac t_induction >>
 srw_tac[] [type_subst_def, infer_type_subst_def, t_walkstar_eqn1]
 >- (every_case_tac >>
     srw_tac[] [t_walkstar_eqn1] >>
     full_simp_tac(srw_ss()) [ALOOKUP_FAILS] >>
     full_simp_tac(srw_ss()) [MAP_ZIP, LENGTH_COUNT_LIST, ALOOKUP_ZIP_MAP_SND] >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [MEM_ZIP, LENGTH_COUNT_LIST] >>
     metis_tac [])
 >- metis_tac []);

val infer_t_induction = infer_tTheory.infer_t_induction;

val infer_subst_FEMPTY = Q.store_thm ("infer_subst_FEMPTY",
`(!t. infer_subst FEMPTY t = t) ∧
 (!ts. MAP (infer_subst FEMPTY) ts = ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [SUBSET_DEF, infer_subst_def] >>
metis_tac []);

val infer_subst_submap = Q.store_thm ("infer_subst_submap",
`(!t s1 s2 m. 
    s1 SUBMAP s2 ∧
    {uv | uv ∈ t_vars t ∧ m ≤ uv} ⊆ FDOM s1 ∧
    (!uv. uv ∈ FDOM s2 DIFF FDOM s1 ⇒ m ≤ uv)
    ⇒
    (infer_subst s1 t = infer_subst s2 t)) ∧
 (!ts s1 s2 m. 
    s1 SUBMAP s2 ∧
    {uv | ?s. uv ∈ s ∧ MEM s (MAP t_vars ts) ∧ m ≤ uv} ⊆ FDOM s1 ∧
    (!uv. uv ∈ FDOM s2 DIFF FDOM s1 ⇒ m ≤ uv)
    ⇒
    (MAP (infer_subst s1) ts = MAP (infer_subst s2) ts))`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [SUBSET_DEF, infer_subst_def, t_vars_eqn] >|
[metis_tac [],
 full_case_tac >>
     full_case_tac >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [SUBMAP_DEF, FLOOKUP_DEF] >>
     metis_tac [],
 metis_tac [],              
 metis_tac []]);

val generalise_subst = Q.store_thm ("generalise_subst",
`(!t m n s tvs s' t'.
  (generalise m n s t = (tvs, s', t'))
  ⇒
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ t_vars t ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (!uv. uv ∈ t_vars t' ⇒ uv < m) ∧
  (infer_subst s' t = infer_subst s t')) ∧
 (!ts m n s tvs s' ts'.
  (generalise_list m n s ts = (tvs, s', ts'))
  ⇒
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ BIGUNION (set (MAP t_vars ts)) ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (!uv. uv ∈  BIGUNION (set (MAP t_vars ts')) ⇒ uv < m) ∧
  (MAP (infer_subst s') ts = MAP (infer_subst s) ts'))`,
Induct >>
SIMP_TAC (srw_ss()) [t_vars_eqn, generalise_def, infer_subst_def] >|
[REPEAT GEN_TAC  >>
     STRIP_TAC >>
     `?tvs s' ts'. generalise_list m n s ts = (tvs, s', ts')`
               by (cases_on `generalise_list m n s ts` >>
                   srw_tac[] [] >>
                   cases_on `r` >>
                   full_simp_tac(srw_ss()) []) >>
     full_simp_tac(srw_ss()) [LET_THM] >>
     srw_tac[] [] >>
     res_tac >>
     srw_tac[] [EXTENSION, infer_subst_def] >>
     full_simp_tac(srw_ss()) [t_vars_eqn] >>
     metis_tac [],
 srw_tac[] [] >>
     every_case_tac >>
     full_simp_tac(srw_ss()) [] >>
     srw_tac[] [] >>
     srw_tac[] [FLOOKUP_DEF, EXTENSION] >>
     TRY (EQ_TAC) >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [FLOOKUP_DEF, infer_subst_def, t_vars_eqn] >>
     decide_tac,
 REPEAT GEN_TAC >>
     STRIP_TAC >>
     `?tvs s' t'. generalise m n s t = (tvs, s', t')`
               by (cases_on `generalise m n s t` >>
                   srw_tac[] [] >>
                   cases_on `r` >>
                   full_simp_tac(srw_ss()) []) >>
     full_simp_tac(srw_ss()) [LET_THM] >>
     `?tvs s' ts'. generalise_list m (tvs'+n) s'' ts = (tvs, s', ts')`
               by (cases_on `generalise_list m (tvs'+n) s'' ts` >>
                   srw_tac[] [] >>
                   cases_on `r` >>
                   full_simp_tac(srw_ss()) []) >>
     full_simp_tac(srw_ss()) [LET_THM] >>
     qpat_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `tvs'+n`, `s''`, `tvs''`, `s'''`, `ts''`]) >>
     qpat_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `n`, `s`, `tvs'`, `s''`, `t'`]) >>
     srw_tac[] [INTER_UNION] >|
     [metis_tac [SUBMAP_TRANS],
      srw_tac[] [EXTENSION] >>
          metis_tac [],
      `uv ∈ FDOM s''` by full_simp_tac(srw_ss()) [] >>
          res_tac >>
          srw_tac[] [INTER_UNION] >>
          full_simp_tac(srw_ss()) [SUBMAP_DEF],
      `uv ∈ FDOM s''` by full_simp_tac(srw_ss()) [] >>
          res_tac >>
          srw_tac[] [INTER_UNION] >>
          full_simp_tac(srw_ss()) [SUBMAP_DEF] >>
          res_tac >>
          decide_tac,
      `uv ∈ FDOM s'` by (full_simp_tac(srw_ss()) [] >> metis_tac []) >>
          cases_on `uv ∈ t_vars t` >>
          srw_tac[] [] >>
          res_tac >>
          srw_tac[] [INTER_UNION] >>
          full_simp_tac(srw_ss()) [SUBMAP_DEF] >>
          res_tac >>
          decide_tac,
      `uv ∈ FDOM s'` by (full_simp_tac(srw_ss()) [] >> metis_tac []) >>
          cases_on `uv ∈ t_vars t` >>
          srw_tac[] [] >|
          [`uv ∈ FDOM s''` by (full_simp_tac(srw_ss()) [] >> metis_tac []) >>
               res_tac >>
               srw_tac[] [INTER_UNION] >>
               full_simp_tac(srw_ss()) [SUBMAP_DEF] >>
               res_tac >>
               decide_tac,
           res_tac >>
               srw_tac[] [INTER_UNION] >>
               full_simp_tac(srw_ss()) [SUBMAP_DEF] >>
               decide_tac],
      metis_tac [],
      metis_tac [],
      `{uv | uv ∈ t_vars t ∧ m ≤ uv} ⊆ FDOM s'' ∧ (!uv. uv ∈ FDOM s' DIFF FDOM s'' ⇒ m ≤ uv)`
               by srw_tac[] [SUBSET_DEF] >>
          metis_tac [infer_subst_submap],
      `{uv | ∃s. uv ∈ s ∧ MEM s (MAP t_vars ts'') ∧ m ≤ uv} ⊆ FDOM s ∧ (!uv. uv ∈ FDOM s'' DIFF FDOM s ⇒ m ≤ uv)`
                     by (srw_tac[] [SUBSET_DEF] >>
                         `¬(x < m)` by decide_tac  >>
                         metis_tac []) >>
          metis_tac [infer_subst_submap]]]);

val generalise_subst_empty = Q.store_thm ("generalise_subst_empty",
`!n ts tvs s ts'.
  (generalise_list 0 n FEMPTY ts = (tvs, s, ts'))
  ⇒
  (FDOM s = { uv | uv ∈ BIGUNION (set (MAP t_vars ts)) }) ∧
  (!uv. uv ∈ FDOM s ⇒ ∃tv. (FAPPLY s uv = tv) ∧ tv < tvs + n) ∧
  (BIGUNION (set (MAP t_vars ts')) = {}) ∧
  (ts' = MAP (infer_subst s) ts)`,
srw_tac[] [] >>
imp_res_tac generalise_subst >>
full_simp_tac(srw_ss()) [] >>
srw_tac[] [] >|
[srw_tac[] [BIGUNION, EXTENSION] >>
     metis_tac [],
 full_simp_tac(srw_ss()) [EXTENSION] >>
     metis_tac [],
 cases_on `ts'` >>
     srw_tac[] [] >>
     srw_tac[] [EXTENSION] >>
     eq_tac >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [t_vars_eqn] >>
     metis_tac [],
 metis_tac [infer_subst_FEMPTY]]);

(* ---------- Dealing with the monad ---------- *)

val infer_st_rewrs = Q.store_thm ("infer_st_rewrs",
`(!st. (st with next_uvar := st.next_uvar) = st) ∧
 (!st. (st with subst := st.subst) = st) ∧
 (!st s. (st with subst := s).subst = s) ∧
 (!st s. (st with subst := s).next_uvar = st.next_uvar) ∧
 (!st uv. (st with next_uvar := uv).next_uvar = uv) ∧
 (!st uv. (st with next_uvar := uv).subst = st.subst)`,
srw_tac[] [] >>
cases_on `st` >>
srw_tac[] [infer_st_component_equality]);

val st_ex_return_success = Q.prove (
`!v st v' st'.
  (st_ex_return v st = (Success v', st')) =
  ((v = v') ∧ (st = st'))`,
srw_tac[] [st_ex_return_def]);

val st_ex_bind_success = Q.prove (
`!f g st st' v. 
 (st_ex_bind f g st = (Success v, st')) =
 ?v' st''. (f st = (Success v', st'')) /\ (g v' st'' = (Success v, st'))`,
srw_tac[] [st_ex_bind_def] >>
cases_on `f st` >>
srw_tac[] [] >>
cases_on `q` >>
srw_tac[] []);

val fresh_uvar_success = Q.prove (
`!st t st'. 
  (fresh_uvar st = (Success t, st')) =
  ((t = Infer_Tuvar st.next_uvar) ∧
   (st' = st with next_uvar := st.next_uvar + 1))`,
srw_tac[] [fresh_uvar_def] >>
metis_tac []);

val n_fresh_uvar_success = Q.prove (
`!n st ts st'. 
  (n_fresh_uvar n st = (Success ts, st')) =
  ((ts = MAP (\n. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST n)) ∧
   (st' = st with next_uvar := st.next_uvar + n))`,
ho_match_mp_tac n_fresh_uvar_ind >>
srw_tac[] [] >>
srw_tac[] [st_ex_return_success, Once n_fresh_uvar_def, COUNT_LIST_SNOC,
    st_ex_bind_success, fresh_uvar_success, infer_st_rewrs] >-
metis_tac [] >>
full_simp_tac(srw_ss()) [] >>
srw_tac [ARITH_ss] [] >>
srw_tac[] [count_list_sub1, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
eq_tac >>
srw_tac [ARITH_ss] [arithmeticTheory.ADD1]);

val apply_subst_success = Q.prove (
`!t1 st1 t2 st2.
  (apply_subst t1 st1 = (Success t2, st2))
  =
  ((st2 = st1) ∧
   (t2 = t_walkstar st1.subst t1))`,
srw_tac[] [st_ex_return_def, st_ex_bind_def, LET_THM, apply_subst_def, read_def] >>
eq_tac >>
srw_tac[] []);

val add_constraint_success = Q.store_thm ("add_constraint_success",
`!t1 t2 st st' x.
  (add_constraint t1 t2 st = (Success x, st'))
  =
  ((x = ()) ∧ (?s. (t_unify st.subst t1 t2 = SOME s) ∧ (st' = st with subst := s)))`,
srw_tac[] [add_constraint_def] >>
full_case_tac >>
metis_tac []);

val add_constraints_success = Q.prove (
`!ts1 ts2 st st' x.
  (add_constraints ts1 ts2 st = (Success x, st'))
  =
  ((LENGTH ts1 = LENGTH ts2) ∧ 
   ((x = ()) ∧ 
   (st.next_uvar = st'.next_uvar) ∧
   pure_add_constraints st.subst (ZIP (ts1,ts2)) st'.subst))`,
ho_match_mp_tac add_constraints_ind >>
srw_tac[] [add_constraints_def, pure_add_constraints_def, st_ex_return_success,
    failwith_def, st_ex_bind_success, add_constraint_success] >>
TRY (cases_on `x`) >>
srw_tac[] [pure_add_constraints_def] >-
metis_tac [infer_st_component_equality] >>
eq_tac >>
srw_tac[] [] >>
full_simp_tac(srw_ss()) [infer_st_subst] >>
cases_on `t_unify st.subst t1 t2` >>
full_simp_tac(srw_ss()) []);

val failwith_success = Q.prove (
`!m st v st'. (failwith m st = (Success v, st')) = F`,
srw_tac[] [failwith_def]);

val lookup_st_ex_success = Q.prove (
`!pr x l st v st'. 
  (lookup_st_ex pr x l st = (Success v, st'))
  =
  ((ALOOKUP l x = SOME v) ∧ (st = st'))`,
ho_match_mp_tac lookup_st_ex_ind >>
srw_tac[] [lookup_st_ex_def, failwith_def, st_ex_return_success]);

val flookup_st_ex_success = Q.prove (
`!pr x l st v st'. 
  (flookup_st_ex pr x l st = (Success v, st'))
  =
  ((FLOOKUP l x = SOME v) ∧ (st = st'))`,
srw_tac[] [flookup_st_ex_def] >>
every_case_tac >>
full_simp_tac(srw_ss()) [failwith_def, st_ex_return_success]);

val lookup_tenvC_st_ex_success = Q.prove (
`!cn l st v st'. 
  (lookup_tenvC_st_ex cn l st = (Success v, st'))
  =
  ((lookup_alist_mod_env cn l = SOME v) ∧ (st = st'))`,
 srw_tac[] [] >>
 cases_on `cn` >>
 PairCases_on `l` >>
 srw_tac[] [lookup_tenvC_st_ex_def, lookup_st_ex_success, lookup_alist_mod_env_def,
     st_ex_bind_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [lookup_st_ex_success] >>
 induct_on `l0` >>
 srw_tac[] [] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss()) [lookup_st_ex_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [st_ex_return_def]);

val op_case_expand = Q.prove (
`!f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 op st v st'.
  ((case op of
       Opn opn => f1
     | Opb opb => f2
     | Equality => f3
     | Opapp => f4
     | Opassign => f5
     | Opref => f6
     | Opderef => f7
     | Aw8length => f8
     | Aw8alloc => f9
     | Aw8sub => f10
     | Aw8update => f11
     | Ord => f12
     | Chr => f13
     | Chopb opb => f14
     | Explode => f15
     | Implode => f16
     | Strlen => f17
     | VfromList => f18
     | Vsub => f19
     | Vlength => f20
     | Alength => f21
     | Aalloc => f22
     | Asub => f23
     | Aupdate => f24) st
   = (Success v, st'))
  =
  ((?opn. (op = Opn opn) ∧ (f1 st = (Success v, st'))) ∨
   (?opb. (op = Opb opb) ∧ (f2 st = (Success v, st'))) ∨
   ((op = Equality) ∧ (f3 st = (Success v, st'))) ∨
   ((op = Opapp) ∧ (f4 st = (Success v, st'))) ∨
   ((op = Opassign) ∧ (f5 st = (Success v, st'))) ∨
   ((op = Opref) ∧ (f6 st = (Success v, st'))) ∨
   ((op = Opderef) ∧ (f7 st = (Success v, st'))) ∨
   ((op = Aw8length) ∧ (f8 st = (Success v, st'))) ∨
   ((op = Aw8alloc) ∧ (f9 st = (Success v, st'))) ∨
   ((op = Aw8sub) ∧ (f10 st = (Success v, st'))) ∨
   ((op = Aw8update) ∧ (f11 st = (Success v, st'))) ∨
   ((op = Ord) ∧ (f12 st = (Success v, st'))) ∨
   ((op = Chr) ∧ (f13 st = (Success v, st'))) ∨
   (?opb. (op = Chopb opb)) ∧ (f14 st = (Success v, st')) ∨
   ((op = Explode) ∧ (f15 st = (Success v, st'))) ∨
   ((op = Implode) ∧ (f16 st = (Success v, st'))) ∨
   ((op = Strlen) ∧ (f17 st = (Success v, st'))) ∨
   ((op = VfromList) ∧ (f18 st = (Success v, st'))) ∨
   ((op = Vsub) ∧ (f19 st = (Success v, st'))) ∨
   ((op = Vlength) ∧ (f20 st = (Success v, st'))) ∨
   ((op = Alength) ∧ (f21 st = (Success v, st'))) ∨
   ((op = Aalloc) ∧ (f22 st = (Success v, st'))) ∨
   ((op = Asub) ∧ (f23 st = (Success v, st'))) ∨
   ((op = Aupdate) ∧ (f24 st = (Success v, st'))))`,
srw_tac[] [] >>
cases_on `op` >>
srw_tac[] []);

val constrain_op_success = 
  SIMP_CONV (srw_ss()) [constrain_op_def, op_case_expand, st_ex_bind_success,
                        st_ex_return_success, add_constraint_success]
  ``(constrain_op op ts st = (Success v, st'))``

val _ = save_thm ("constrain_op_success", constrain_op_success);

val get_next_uvar_success = Q.prove (
`!st v st'. 
  (get_next_uvar st = (Success v, st')) 
  =
  ((v = st.next_uvar) ∧ (st = st'))`,
srw_tac[] [get_next_uvar_def] >>
metis_tac []);

val apply_subst_list_success =
  SIMP_CONV (srw_ss()) [apply_subst_list_def, LET_THM]
  ``(apply_subst_list ts st = (Success v, st'))``

val guard_success = Q.prove (
`∀P m st v st'.
  (guard P m st = (Success v, st'))
  =
  (P ∧ (v = ()) ∧ (st = st'))`,
srw_tac[] [guard_def, st_ex_return_def, failwith_def] >>
metis_tac []);

val option_case_eq = Q.prove (
`!opt f g v st st'.
  ((case opt of NONE => f | SOME x => g x) st = (Success v, st')) =
  (((opt = NONE) ∧ (f st = (Success v, st'))) ∨ (?x. (opt = SOME x) ∧ (g x st = (Success v, st'))))`,
srw_tac[] [] >>
cases_on `opt` >>
full_simp_tac(srw_ss()) []);

val success_eqns = 
  LIST_CONJ [st_ex_return_success, st_ex_bind_success, fresh_uvar_success,
             apply_subst_success, add_constraint_success, lookup_st_ex_success,
             n_fresh_uvar_success, failwith_success, add_constraints_success,
             oneTheory.one,flookup_st_ex_success,
             get_next_uvar_success, apply_subst_list_success, guard_success,
             read_def, option_case_eq, lookup_tenvC_st_ex_success];

val _ = save_thm ("success_eqns", success_eqns);

(* ---------- Simple structural properties ---------- *)

val remove_pair_lem = Q.store_thm ("remove_pair_lem",
`(!f v. (\(x,y). f x y) v = f (FST v) (SND v)) ∧
 (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND (SND v)))`,
srw_tac[] [] >>
PairCases_on `v` >>
srw_tac[] []);

val infer_funs_length = Q.store_thm ("infer_funs_length",
`!menv cenv env funs ts st1 st2.
  (infer_funs menv cenv env funs st1 = (Success ts, st2)) ⇒
  (LENGTH funs = LENGTH ts)`,
induct_on `funs` >>
srw_tac[] [infer_e_def, success_eqns] >>
srw_tac[] [] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [infer_e_def, success_eqns] >>
srw_tac[] [] >>
metis_tac []);

val infer_p_bindings = Q.store_thm ("infer_p_bindings",
`(!cenv p st t env st' x.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    (pat_bindings p x = MAP FST env ++ x)) ∧
 (!cenv ps st ts env st' x.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    (pats_bindings ps x = MAP FST env ++ x))`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [pat_bindings_def, infer_p_def, success_eqns, remove_pair_lem] >>
srw_tac[] [] >|
[PairCases_on `v'` >>
     srw_tac[] [] >>
     metis_tac [],
 PairCases_on `v''` >>
     srw_tac[] [] >>
     metis_tac [],
 PairCases_on `v'` >>
     srw_tac[] [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     srw_tac[] [] >>
     metis_tac [APPEND_ASSOC]]);

(* ---------- Dealing with the constraint set ---------- *)

val pure_add_constraints_append2 = Q.prove (
`!s1 ts s2 t1 t2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
induct_on `ts` >>
srw_tac[] [pure_add_constraints_def] >>
srw_tac[] [] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [pure_add_constraints_def] >>
metis_tac [t_unify_wfs, t_unify_apply2]);

val pure_add_constraints_apply = Q.store_thm ("pure_add_constraints_apply",
`!s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts`,
induct_on `ts` >>
srw_tac[] [pure_add_constraints_def] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [pure_add_constraints_def] >>
metis_tac [t_unify_apply, pure_add_constraints_append2, t_unify_wfs]);

val pure_add_constraints_append = Q.store_thm ("pure_add_constraints_append",
`!s1 ts1 s3 ts2. 
  pure_add_constraints s1 (ts1 ++ ts2) s3
  =
  (?s2. pure_add_constraints s1 ts1 s2 ∧ pure_add_constraints s2 ts2 s3)`,
ho_match_mp_tac pure_add_constraints_ind >>
srw_tac[] [pure_add_constraints_def] >>
metis_tac []);

val infer_p_constraints = Q.store_thm ("infer_p_constraints",
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    (?ts'. pure_add_constraints st.subst ts' st'.subst))`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def]);

val infer_e_constraints = Q.store_thm ("infer_e_constraints",
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst))`,
ho_match_mp_tac infer_e_ind >>
srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
TRY (cases_on `v'`) >>
every_case_tac >>
full_simp_tac(srw_ss()) [success_eqns] >>
srw_tac[] [] >>
full_simp_tac(srw_ss()) [infer_st_rewrs] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, infer_p_constraints]);

val pure_add_constraints_wfs = Q.store_thm ("pure_add_constraints_wfs",
`!s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  t_wfs s2`,
induct_on `ts` >>
srw_tac[] [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

(* ---------- The next unification variable is monotone non-decreasing ---------- *)

val infer_p_next_uvar_mono = Q.store_thm ("infer_p_next_uvar_mono",
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
metis_tac [DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``,
           arithmeticTheory.LESS_EQ_TRANS]);

val infer_e_next_uvar_mono = Q.store_thm ("infer_e_next_uvar_mono",
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env funs st st' ts.
    (infer_funs menv cenv env funs st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)`,
ho_match_mp_tac infer_e_ind >>
srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
every_case_tac >>
full_simp_tac(srw_ss()) [success_eqns] >>
metis_tac [infer_p_next_uvar_mono, arithmeticTheory.LESS_EQ_TRANS,
           pair_CASES,
           DECIDE ``!(x:num) y. x ≤ x + y``,
           DECIDE ``!(x:num) y. x + 1 ≤ y ⇒ x ≤ y``,
           DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``]);

(* ---------- The inferencer builds well-formed substitutions ---------- *)

val infer_p_wfs = Q.store_thm ("infer_p_wfs",
`(!cenv p st t env st'.
    t_wfs st.subst ∧
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    t_wfs st'.subst) ∧
 (!cenv ps st ts env st'.
    t_wfs st.subst ∧
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
   t_wfs st'.subst)`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
prove_tac [pure_add_constraints_wfs]);

val infer_e_wfs = Q.store_thm ("infer_e_wfs",
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst)`,
ho_match_mp_tac infer_e_ind >>
srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
full_simp_tac(srw_ss()) [] >>
res_tac >>
imp_res_tac t_unify_wfs >>
full_simp_tac(srw_ss()) [] >>
imp_res_tac pure_add_constraints_wfs >>
full_simp_tac(srw_ss()) [] >>
TRY (cases_on `v'`) >>
imp_res_tac infer_p_wfs >>
full_simp_tac(srw_ss()) [] >>
every_case_tac >>
full_simp_tac(srw_ss()) [success_eqns] >>
srw_tac[] [] >>
full_simp_tac(srw_ss()) [infer_st_rewrs] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
imp_res_tac t_unify_wfs);

(* ---------- The invariants of the inferencer ---------- *)

val check_env_bind = Q.store_thm ("check_env_bind",
`!uvs x tvs t env.
  check_env uvs ((x,(tvs,t))::env) = (check_t tvs uvs t ∧ check_env uvs env)`,
 srw_tac[] [check_env_def]);

val check_env_lookup = Q.store_thm ("check_env_lookup",
`!uvs n env tvs t.
  check_env uvs env ∧
  (ALOOKUP env n = SOME (tvs,t))
  ⇒
  check_t tvs uvs t`,
 induct_on `env` >>
 srw_tac[] [check_t_def] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss()) [] >>
 every_case_tac >>
 srw_tac[] [] >>
 full_simp_tac(srw_ss()) [check_env_bind] >>
 metis_tac []);

val check_menv_lookup = Q.store_thm ("check_menv_lookup",
`!menv mn n env tvs t.
  check_menv menv ∧
  (FLOOKUP menv mn = SOME env) ∧
  (ALOOKUP env n = SOME (tvs,t))
  ⇒
  check_t tvs {} t`,
 srw_tac[] [check_menv_def] >>
 imp_res_tac FEVERY_FLOOKUP >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss()) [EVERY_MEM] >>
 res_tac >>
 full_simp_tac(srw_ss()) []);

val check_cenv_lookup = Q.store_thm ("check_cenv_lookup",
`!cenv cn tvs ts t.
  check_cenv cenv ∧
  (lookup_alist_mod_env cn cenv = SOME (tvs,ts,t))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 srw_tac[] [] >>
 PairCases_on `cenv` >>
 full_simp_tac(srw_ss()) [lookup_alist_mod_env_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [check_flat_cenv_def, EVERY_MEM, check_cenv_def] >>
 srw_tac[] [] >>
 imp_res_tac ALOOKUP_MEM >>
 res_tac >>
 full_simp_tac(srw_ss()) [] >>
 res_tac >>
 full_simp_tac(srw_ss()) []);

val check_t_more = Q.store_thm ("check_t_more",
`(!t tvs. check_t tvs {} t ⇒ !uvs. check_t tvs uvs t) ∧
 (!ts tvs. EVERY (check_t tvs {}) ts ⇒ !uvs. EVERY (check_t tvs uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def] >>
metis_tac []);

val check_t_more2 = Q.store_thm ("check_t_more2",
`(!t tvs uvs. check_t tvs uvs t ⇒ !tvs'. check_t (tvs' + tvs) uvs t) ∧
 (!ts tvs uvs. EVERY (check_t tvs uvs) ts ⇒ !tvs'. EVERY (check_t (tvs' + tvs) uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def] >-
decide_tac >>
metis_tac []);

val check_t_more3 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. check_t tvs (count (uvs + uvs')) t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. EVERY (check_t tvs (count (uvs + uvs'))) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def] >-
metis_tac [] >>
decide_tac);

val check_t_more4 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. uvs ≤ uvs' ⇒ check_t tvs (count uvs') t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. uvs ≤ uvs' ⇒ EVERY (check_t tvs (count uvs')) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac [ARITH_ss] [check_t_def] >>
metis_tac []);

val check_t_more5 = Q.store_thm ("check_t_more5",
`(!t uvs tvs. check_t tvs uvs t ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_t tvs uvs' t) ∧
 (!ts uvs tvs. EVERY (check_t tvs uvs) ts ⇒ !uvs'. uvs ⊆ uvs' ⇒ EVERY (check_t tvs uvs') ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def, SUBSET_DEF] >>
metis_tac []);

val check_t_t_vars = Q.store_thm ("check_t_t_vars",
`!tvs uvs t.
  check_t tvs uvs t ⇒ t_vars t ⊆ uvs`,
ho_match_mp_tac check_t_ind >>
srw_tac[] [t_vars_eqn, check_t_def, EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
metis_tac []);

val check_s_more = Q.prove (
`!s tvs uvs. check_s tvs (count uvs) s ⇒ check_s tvs (count (uvs + 1)) s`,
srw_tac[] [check_s_def] >>
metis_tac [check_t_more3]);

val check_s_more2 = Q.store_thm ("check_s_more2",
`!s uvs. check_s tvs (count uvs) s ⇒ !uvs'. uvs ≤ uvs' ⇒ check_s tvs (count uvs') s`,
srw_tac[] [check_s_def] >>
metis_tac [check_t_more4]);

val check_s_more3 = Q.store_thm ("check_s_more3",
`!s uvs. check_s tvs uvs s ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_s tvs uvs' s`,
srw_tac[] [check_s_def] >>
metis_tac [check_t_more5]);

val check_t_deBruijn_inc2 = Q.prove (
`!inc t. check_t tvs {} t ⇒ check_t (inc + tvs) {} (infer_deBruijn_inc inc t)`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
srw_tac[] [check_t_def, infer_deBruijn_inc_def] >>
full_simp_tac(srw_ss()) [EVERY_MAP, EVERY_MEM]);

val check_t_deBruijn_inc = Q.store_thm ("check_t_deBruijn_inc",
`!inc t. check_t 0 UNIV t ⇒ (infer_deBruijn_inc inc t = t)`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
srw_tac[] [check_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
srw_tac[] []);

val check_t_subst = Q.store_thm ("check_t_subst",
`!tvs (tvs':num set) t s. 
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`,
ho_match_mp_tac check_t_ind >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
full_simp_tac(srw_ss()) [t_walkstar_eqn1] >>
induct_on `ts` >>
srw_tac[] []);

val t_vwalk_check = Q.store_thm ("t_vwalk_check",
`!s. t_wfs s ⇒ 
  !n tvs uvs t. 
    n ∈ uvs ∧ 
    check_s tvs uvs s
    ⇒
    check_t tvs uvs (t_vwalk s n)`,
NTAC 2 STRIP_TAC >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
pop_assum ho_match_mp_tac >>
srw_tac[] [] >>
srw_tac[] [Once t_vwalk_eqn] >>
cases_on `FLOOKUP s n` >>
srw_tac[] [check_t_def] >>
cases_on `x` >>
srw_tac[] [check_t_def] >>
full_simp_tac(srw_ss()) [check_s_def, FLOOKUP_DEF] >>
metis_tac [check_t_def, IN_UNION]);

val t_walkstar_check' = Q.prove (
`!s. t_wfs s ⇒
  !t tvs uvs. 
    check_s tvs (uvs ∪ FDOM s) s ∧
    check_t tvs (uvs ∪ FDOM s) t
    ⇒
    check_t tvs uvs (t_walkstar s t)`,
NTAC 2 STRIP_TAC >>
imp_res_tac t_walkstar_ind >>
pop_assum ho_match_mp_tac >>
srw_tac[] [] >>
srw_tac[] [t_walkstar_eqn] >>
cases_on `t` >>
full_simp_tac(srw_ss()) [check_t_def] >>
srw_tac[] [t_walk_eqn] >>
srw_tac[] [check_t_def, EVERY_MAP] >|
[full_simp_tac(srw_ss()) [EVERY_MEM] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [t_walk_eqn],
 full_simp_tac(srw_ss()) [t_walk_eqn] >>
     `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)`
             by metis_tac [t_vwalk_check,  IN_UNION] >>
     cases_on `t_vwalk s n` >>
     full_simp_tac(srw_ss()) [check_t_def, EVERY_MAP] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     metis_tac [t_vwalk_to_var],
 full_simp_tac(srw_ss()) [t_walk_eqn] >>
     `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)`
             by metis_tac [t_vwalk_check,  IN_UNION] >>
     cases_on `t_vwalk s n` >>
     full_simp_tac(srw_ss()) [check_t_def, EVERY_MAP] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     metis_tac [t_vwalk_to_var]]);

val t_walkstar_check = Q.store_thm ("t_walkstar_check",
`!s t tvs uvs. 
    t_wfs s ∧
    check_s tvs (uvs ∪ FDOM s) s ∧
    check_t tvs (uvs ∪ FDOM s) t
    ⇒
    check_t tvs uvs (t_walkstar s t)`,
metis_tac [t_walkstar_check']);

val t_unify_check_s_help = Q.prove (
`(!s t1 t2. t_wfs s ⇒ 
    !tvs uvs s'. check_s tvs uvs s ∧
           check_t tvs uvs t1 ∧
           check_t tvs uvs t2 ∧
           (t_unify s t1 t2 = SOME s')
           ⇒
           check_s tvs uvs s') ∧
 (!s ts1 ts2. t_wfs s ⇒ 
    !tvs uvs s'. check_s tvs uvs s ∧
           EVERY (check_t tvs uvs) ts1 ∧
           EVERY (check_t tvs uvs) ts2 ∧
           (ts_unify s ts1 ts2 = SOME s')
           ⇒
           check_s tvs uvs s')`,
ho_match_mp_tac t_unify_strongind >>
srw_tac[] [] >|
[qpat_assum `t_unify s t1 t2 = SOME s'` mp_tac >>
     srw_tac[] [t_unify_eqn] >>
     cases_on `t1` >>
     cases_on `t2` >>
     full_simp_tac(srw_ss()) [t_walk_eqn, t_ext_s_check_eqn, check_t_def] >|
     [`check_t tvs uvs (t_vwalk s n')` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n'` >>
          full_simp_tac(srw_ss()) [check_t_def] >>
          full_simp_tac(srw_ss()) [check_s_def] >>
          srw_tac[] [check_t_def] >>
          srw_tac[] [check_t_def, FAPPLY_FUPDATE_THM],
      metis_tac [],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          full_simp_tac(srw_ss()) [check_t_def] >-
          metis_tac [] >>
          full_simp_tac(srw_ss()) [check_s_def] >>
          srw_tac[] [check_t_def] >>
          srw_tac[] [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          full_simp_tac(srw_ss()) [check_t_def] >>
          full_simp_tac(srw_ss()) [check_s_def] >>
          srw_tac[] [check_t_def] >>
          srw_tac[] [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          full_simp_tac(srw_ss()) [check_t_def] >-
          metis_tac [] >>
          full_simp_tac(srw_ss()) [check_s_def] >>
          srw_tac[] [check_t_def] >>
          srw_tac[] [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          `check_t tvs uvs (t_vwalk s n')` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n'` >>
          full_simp_tac(srw_ss()) [check_t_def] >>
          TRY (full_simp_tac(srw_ss()) [check_s_def] >>
               srw_tac[] [check_t_def, FAPPLY_FUPDATE_THM] >>
               srw_tac[] [check_t_def] >>
               NO_TAC) >>
          metis_tac []],
 pop_assum mp_tac >>
     cases_on `ts1` >>
     cases_on `ts2` >>
     full_simp_tac(srw_ss()) [ts_unify_def] >>
     srw_tac[] [] >-
     metis_tac [] >>
     cases_on `t_unify s h h'` >>
     full_simp_tac(srw_ss()) []]);

val check_t_walkstar = Q.store_thm ("check_t_walkstar",
`(!t tvs s.
    t_wfs s ∧
    check_t 0 (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    check_t tvs {} (t_walkstar s t)) ∧
 (!ts tvs s.
    t_wfs s ∧
    EVERY (check_t 0 (FDOM s)) ts ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    EVERY (check_t tvs {} o t_walkstar s) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def, t_walkstar_eqn1, EVERY_MAP] >>
metis_tac []);

val t_walkstar_no_vars = Q.store_thm ("t_walkstar_no_vars",
`!tvs (tvs':num set) t s. 
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t_walkstar s t = t)`,
ho_match_mp_tac check_t_ind >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
full_simp_tac(srw_ss()) [t_walkstar_eqn1] >>
induct_on `ts` >>
srw_tac[] [] >>
metis_tac []);

val t_unify_check_s = Q.store_thm ("t_unify_check_s",
`!s1 tvs uvs t1 t2 s2.
  t_wfs s1 ∧
  check_s tvs uvs s1 ∧ 
  check_t tvs uvs t1 ∧
  check_t tvs uvs t2 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  check_s tvs uvs s2`,
metis_tac [t_unify_check_s_help]);

val pure_add_constraints_check_s = Q.store_thm ("pure_add_constraints_check_s",
`!s1 tvs uvs ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2 ∧
  EVERY (\(t1,t2). check_t tvs (count uvs) t1 ∧ check_t tvs (count uvs) t2) ts ∧
  check_s tvs (count uvs) s1
  ⇒
  check_s tvs (count uvs) s2`,
induct_on `ts` >-
(srw_tac[] [check_s_def, pure_add_constraints_def] >-
 metis_tac []) >>
srw_tac[] [pure_add_constraints_def] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [pure_add_constraints_def] >>
metis_tac [t_unify_wfs, t_unify_check_s]);

val infer_p_check_t = Q.store_thm ("infer_p_check_t",
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    check_t 0 (count st'.next_uvar) t) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    EVERY (check_t 0 (count st'.next_uvar)) ts)`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [infer_p_def, success_eqns, remove_pair_lem] >>
srw_tac[] [check_t_def] >|
[PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [remove_pair_lem, EVERY_MEM] >>
     srw_tac[] [] >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [],
 PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
     srw_tac[] [check_t_def] >>
     `?n. st'.next_uvar = st'''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st'''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
     srw_tac[] [check_t_def] >>
     decide_tac,
 PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [],
 PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [infer_p_wfs],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [remove_pair_lem, EVERY_MEM] >>
     srw_tac[] [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [infer_p_wfs, check_t_more3]]);

val check_infer_type_subst = Q.prove (
`(!t tvs uvs.
  check_freevars 0 tvs t
  ⇒
  check_t 0 (count (LENGTH tvs + uvs)) (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs)))) t)) ∧
 (!ts tvs uvs.
  EVERY (check_freevars 0 tvs) ts
  ⇒
  EVERY (\t. check_t 0 (count (LENGTH tvs + uvs)) (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs)))) t)) ts)`,
ho_match_mp_tac t_induction >>
srw_tac[] [check_freevars_def, check_t_def, infer_type_subst_def] >|
[pop_assum mp_tac >>
     Q.SPEC_TAC (`uvs`, `uvs`) >>
     induct_on `tvs` >>
     srw_tac[] [COUNT_LIST_def, check_t_def] >>
     qpat_assum `!uvs. P uvs` (mp_tac o Q.SPEC `SUC uvs`) >>
     srw_tac[] [MAP_MAP_o, combinTheory.o_DEF] >>
     full_simp_tac(srw_ss()) [DECIDE ``SUC a + b = a + SUC b``],
 metis_tac [EVERY_MAP]]);

val infer_p_check_s = Q.store_thm ("infer_p_check_s",
`(!cenv p st t env st' tvs.
    (infer_p cenv p st = (Success (t,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!cenv ps st ts env st' tvs.
    (infer_ps cenv ps st = (Success (ts,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst)`,
ho_match_mp_tac infer_p_ind >>
srw_tac[] [infer_p_def, success_eqns, remove_pair_lem] >>
srw_tac[] [] >|
[metis_tac [check_s_more],
 PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono],
 PairCases_on `v''` >>
     full_simp_tac(srw_ss()) [] >>
     res_tac >>
     imp_res_tac infer_p_wfs >>
     `st'''.next_uvar ≤ st'''.next_uvar + LENGTH (FST v')` by decide_tac >>
     `check_s tvs (count st'.next_uvar) st'''.subst` by metis_tac [check_s_more2] >>
     match_mp_tac pure_add_constraints_check_s >>
     qexists_tac `st'''.subst` >>
     qexists_tac `(ZIP (v''0, MAP (infer_type_subst (ZIP (FST v', MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH (FST v')))))) (FST (SND v'))))` >>
     srw_tac[] [] >>
     srw_tac[] [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
     metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_p_next_uvar_mono,
                arithmeticTheory.LESS_EQ_TRANS, infer_p_check_t] >>
     PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [] >>
     imp_res_tac check_cenv_lookup >>
     imp_res_tac check_infer_type_subst >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM],
 PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     metis_tac [infer_p_wfs, check_s_more2, infer_p_next_uvar_mono]]);

val check_env_more = Q.store_thm ("check_env_more",
`!uvs env. check_env (count uvs) env ⇒ !uvs'. uvs ≤ uvs' ⇒ check_env (count uvs') env`,
srw_tac[] [check_env_def, EVERY_MEM] >>
PairCases_on `e` >>
srw_tac[] [] >>
res_tac >>
full_simp_tac(srw_ss()) [] >>
metis_tac [check_t_more4]);

val check_env_merge = Q.store_thm ("check_env_merge",
`!uvs env1 env2. check_env uvs (env1 ++ env2) = (check_env uvs env1 ∧ check_env uvs env2)`,
srw_tac[] [check_env_def]);

val check_env_letrec_lem = Q.store_thm ("check_env_letrec_lem",
`∀uvs funs uvs' n.
  check_env (count uvs) (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (uvs' + n)) (COUNT_LIST (LENGTH funs)))) =
  ((funs = []) ∨ (uvs' + LENGTH funs ≤ uvs))`,
induct_on `funs` >>
srw_tac[] [COUNT_LIST_def, check_env_def] >>
cases_on `funs` >>
full_simp_tac(srw_ss()) [COUNT_LIST_def, check_env_def] >>
PairCases_on `h` >>
srw_tac[] [check_t_def] >-
decide_tac >>
srw_tac[] [] >>
PairCases_on `h'` >>
full_simp_tac(srw_ss()) [check_t_def] >>
eq_tac >>
srw_tac [ARITH_ss] [] >>
full_simp_tac(srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] >|
[qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``] >>
     decide_tac,
 qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``,
         DECIDE ``x + (SUC (SUC y)) = x + 1 + SUC y``] >>
     metis_tac []]);

val check_t_infer_db_subst = Q.prove (
`(!t uvs tvs.
   check_t 0 (count (uvs + tvs)) (infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs)) t)
   =
   check_t tvs (count (uvs + tvs)) t) ∧
 (!ts uvs tvs.
   EVERY (check_t 0 (count (uvs + tvs)) o infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs))) ts
   =
   EVERY (check_t tvs (count (uvs + tvs))) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST, 
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >>
metis_tac []);

val check_t_infer_db_subst2 = Q.store_thm ("check_t_infer_db_subst2",
`(!t tvs1 tvs2.
   check_t tvs1  (count tvs2) (infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2)) t)
   =
   check_t (tvs1 + tvs2) (count tvs2) t) ∧
 (!ts tvs1 tvs2.
   EVERY (check_t tvs1 (count tvs2) o infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2))) ts
   =
   EVERY (check_t (tvs1 + tvs2) (count tvs2)) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST, 
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >-
decide_tac >-
decide_tac >-
metis_tac []);

val infer_e_check_t = Q.store_thm ("infer_e_check_t",
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    check_t 0 (count st'.next_uvar) t) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    T) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts')`,
ho_match_mp_tac infer_e_ind >>
srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem] >>
full_simp_tac(srw_ss()) [check_t_def] >>
imp_res_tac infer_e_next_uvar_mono >>
full_simp_tac(srw_ss()) [EVERY_MAP, check_t_def, check_env_bind, check_env_merge, check_t_infer_db_subst] >|
[metis_tac [check_t_more4],
 PairCases_on `v'` >>
     imp_res_tac check_env_lookup >>
     srw_tac[] [] >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     imp_res_tac check_menv_lookup >>
     srw_tac[] [] >>
     metis_tac [check_t_more],
 metis_tac [check_t_more4],
 srw_tac[] [EVERY_MEM, MEM_COUNT_LIST] >>
     decide_tac,
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     full_simp_tac(srw_ss()) [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 every_case_tac >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [infer_st_rewrs, EVERY_MAP, check_t_def, check_env_bind, check_env_merge, check_t_infer_db_subst] >>
     res_tac >>
     full_simp_tac(srw_ss()) [],
 res_tac >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 decide_tac,
 res_tac >>
     full_simp_tac(srw_ss()) [check_t_def] >>
     pop_assum match_mp_tac  >>
     srw_tac[] [opt_bind_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss()) [] >>
     srw_tac[] [check_env_bind] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 res_tac >>
     full_simp_tac(srw_ss()) [check_env_merge, check_env_letrec_lem] >>
     metis_tac [check_env_more, DECIDE ``x + y ≤ z ⇒ x ≤ z:num``],
 res_tac >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     full_simp_tac(srw_ss()) [check_t_def] >>
     metis_tac [check_env_more, check_t_more4, DECIDE ``x ≤ x + 1:num``]]);

val constrain_op_check_s = Q.prove (
`!tvs op ts t st st'.
  t_wfs st.subst ∧
  EVERY (check_t 0 (count st.next_uvar)) ts ∧
  constrain_op op ts st = (Success t, st') ∧
  check_s tvs (count st.next_uvar) st.subst
  ⇒
  check_s tvs (count st'.next_uvar) st'.subst`,
 srw_tac[] [constrain_op_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_int)` by srw_tac[] [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_word8)` by srw_tac[] [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_word8array)` by srw_tac[] [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_string)` by srw_tac[] [check_t_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [success_eqns] >>
 srw_tac[] [] >>
 full_simp_tac(srw_ss()) [infer_st_rewrs]
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar+1)) (Infer_Tapp [h'; Infer_Tuvar st.next_uvar] TC_fn)` 
              by (srw_tac[] [check_t_def] >>
                  metis_tac [check_t_more3]) >>
     `check_t 0 (count (st.next_uvar + 1)) h` 
                    by metis_tac [EVERY_DEF, check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_s tvs (count (st.next_uvar+1)) st.subst`
            by metis_tac [check_s_more] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count st.next_uvar) (Infer_Tapp [h'] TC_ref)` 
              by srw_tac[] [check_t_def] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar+1)) (Infer_Tapp [Infer_Tuvar st.next_uvar] TC_ref)` 
              by (srw_tac[] [check_t_def] >>
                  metis_tac [check_t_more3]) >>
     `check_t 0 (count (st.next_uvar + 1)) h` 
                    by metis_tac [EVERY_DEF, check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_s tvs (count (st.next_uvar+1)) st.subst`
            by metis_tac [check_s_more] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     `check_s tvs (count st.next_uvar) s'`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_char)` by srw_tac[] [check_t_def] >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     CONV_TAC(STRIP_QUANT_CONV(miscLib.lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))) >>
     first_assum(miscLib.match_exists_tac o concl) >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_char)` by srw_tac[] [check_t_def] >>
     metis_tac[t_unify_check_s, t_unify_wfs, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     CONV_TAC(STRIP_QUANT_CONV(miscLib.lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))) >>
     first_assum(miscLib.match_exists_tac o concl) >>
     metis_tac[t_unify_check_s, t_unify_wfs, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short "list")))` by srw_tac[] [check_t_def] >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar + 1)) h`
                    by metis_tac [EVERY_DEF, check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_s tvs (count (st.next_uvar+1)) st.subst`
            by metis_tac [check_s_more] >>
     match_mp_tac t_unify_check_s >>
     qexists_tac `st.subst` >>
     srw_tac[] [] >>
     `check_t tvs (count (st.next_uvar + 1)) 
                  (Infer_Tapp [Infer_Tuvar st.next_uvar] (TC_name (Short "list")))`
                       by (srw_tac[] [check_t_def]) >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     srw_tac[] []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_vector`] >>
         srw_tac[] [] 
         >- metis_tac [check_s_more]
         >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
         >- srw_tac[] [check_t_def])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_vector`] >>
     srw_tac[] []
     >- metis_tac [check_s_more]
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
     >- srw_tac[] [check_t_def])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     srw_tac[] []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_array`] >>
         srw_tac[] [] 
         >- metis_tac [check_s_more]
         >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
         >- srw_tac[] [check_t_def])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE
     ``x ≤ x + 1:num``])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_array`] >>
     srw_tac[] []
     >- metis_tac [check_s_more]
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
     >- srw_tac[] [check_t_def])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     srw_tac[] []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [h''] TC_array`] >>
         srw_tac[] [check_t_def] >>
         metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]));

val infer_e_check_s = Q.store_thm ("infer_e_check_s",
`(!menv cenv env e st st' t tvs.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!menv cenv env es st st' ts tvs.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!menv cenv env pes t1 t2 st st' tvs.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    check_t 0 (count st.next_uvar) t1 ∧
    check_t 0 (count st.next_uvar) t2 ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!menv cenv env funs st st' ts' tvs.
    (infer_funs menv cenv env funs st = (Success ts', st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst)`,
ho_match_mp_tac infer_e_ind >>
srw_tac[] [infer_e_def, success_eqns, remove_pair_lem] >>
srw_tac[] [] >|
[`t_wfs st''.subst` by (metis_tac [infer_e_wfs]) >>
     match_mp_tac check_s_more >>
     match_mp_tac t_unify_check_s >>
     qexists_tac `st''.subst` >>
     qexists_tac `t2` >>
     qexists_tac `Infer_Tapp [] TC_exn` >>
     srw_tac[] [check_t_def] >>
     metis_tac [infer_e_check_t, arithmeticTheory.ADD_0, check_t_more2],
 `t_wfs st''.subst ∧
  check_env (count (st'' with next_uvar := st''.next_uvar).next_uvar) env`
               by metis_tac [check_env_more, infer_e_next_uvar_mono, infer_e_wfs, infer_st_rewrs] >>
     `check_s tvs (count (st'' with next_uvar := st''.next_uvar).next_uvar) (st'' with next_uvar := st''.next_uvar).subst`
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar).next_uvar) t`
               by metis_tac [check_t_more4, infer_e_check_t, infer_st_rewrs] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar).next_uvar) (Infer_Tapp [] TC_exn)`
                  by srw_tac[] [check_t_def] >>
     metis_tac [infer_st_rewrs],
 metis_tac [check_s_more2, DECIDE ``x ≤ x + y:num``],
 metis_tac [check_s_more2, DECIDE ``x ≤ x + y:num``],
 metis_tac [check_s_more2, DECIDE ``x ≤ x + y:num``],
 res_tac >>
     imp_res_tac infer_e_wfs >>
     `st'''.next_uvar ≤ st'''.next_uvar + LENGTH (FST v')` by decide_tac >>
     `check_s tvs (count st'.next_uvar) st'''.subst` by metis_tac [check_s_more2] >>
     match_mp_tac pure_add_constraints_check_s >>
     qexists_tac `st'''.subst` >>
     qexists_tac `(ZIP (ts'', MAP (infer_type_subst (ZIP (FST v', MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH (FST v')))))) (FST (SND v'))))` >>
     srw_tac[] [] >>
     srw_tac[] [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
     metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_e_next_uvar_mono,
                arithmeticTheory.LESS_EQ_TRANS, infer_e_check_t] >>
     PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [] >>
     imp_res_tac check_cenv_lookup >>
     imp_res_tac check_infer_type_subst >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM],
 qpat_assum `!t1. P t1` match_mp_tac >>
     srw_tac[] [] >>
     MAP_EVERY qexists_tac [`Infer_Tuvar st.next_uvar`, `st with next_uvar := st.next_uvar + 1`, `t2`] >>
     srw_tac[] [check_s_more, check_env_bind, check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``],
 `t_wfs st''.subst ∧ 
  EVERY (check_t 0 (count st''.next_uvar)) ts`
          by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     metis_tac [constrain_op_check_s],
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] (TC_name(Short"bool")))` by srw_tac[] [check_t_def] >>
     `t_wfs st'''.subst ∧
      t_wfs st''.subst ∧
      check_env (count st''.next_uvar) env ∧
      check_env (count (st'''.next_uvar)) env ∧
      check_t 0 (count (st'''.next_uvar)) t1 ∧
      check_t 0 (count (st'''.next_uvar)) t2`
                  by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
      full_simp_tac(srw_ss()) [] >>
      `check_s tvs (count st'''.next_uvar) st'''.subst` by metis_tac [] >>
      `t_wfs s` by metis_tac [t_unify_wfs] >>
      match_mp_tac t_unify_check_s >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(is_eq))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      conj_tac >- metis_tac[check_t_more2, arithmeticTheory.ADD_0] >>
      match_mp_tac t_unify_check_s >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(is_eq))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      metis_tac [check_t_more2, arithmeticTheory.ADD_0],
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] (TC_name(Short"bool")))` by srw_tac[] [check_t_def] >>
     `t_wfs st''.subst ∧ t_wfs s`
               by metis_tac [infer_e_wfs, t_unify_wfs] >>
     `t_wfs st''''.subst`
               by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     `t_wfs st'''''.subst`
               by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     `check_env (count st''.next_uvar) env ∧
      check_t 0 (count (st''.next_uvar)) t1`
               by metis_tac [infer_e_check_t, check_env_more, infer_e_next_uvar_mono] >>
     `check_env (count st''''.next_uvar) env ∧
      check_t 0 (count (st''''.next_uvar)) t`
               by metis_tac [infer_e_check_t, check_env_more, infer_e_next_uvar_mono, infer_st_rewrs] >>
     `check_t 0 (count (st'''''.next_uvar)) t ∧
      check_t 0 (count (st'''''.next_uvar)) t3`
              by metis_tac [check_t_more4, infer_e_check_t, check_env_more, infer_e_next_uvar_mono, infer_st_rewrs] >>
     `check_s tvs (count st''.next_uvar) st''.subst` by metis_tac [] >>
     `check_s tvs (count st''.next_uvar) s` by (
       match_mp_tac t_unify_check_s >>
       CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(is_eq))) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       metis_tac [ check_t_more2, arithmeticTheory.ADD_0, infer_st_rewrs] ) >>
     match_mp_tac t_unify_check_s >>
     CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(is_eq))) >>
     first_assum(match_exists_tac o concl) >>
     conj_tac >- simp[] >>
     reverse conj_tac >- simp[] >>
     conj_tac >- ( metis_tac[check_t_more2,arithmeticTheory.ADD_0] ) >>
     first_x_assum(match_mp_tac) >>
     first_assum(match_exists_tac o concl) >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     first_x_assum(match_mp_tac) >>
     first_assum(match_exists_tac o concl) >> simp[],
 `t_wfs st''.subst ∧
  check_env (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) env`
               by metis_tac [check_env_more, infer_e_next_uvar_mono, infer_e_wfs, DECIDE ``x ≤ x + 1:num``,
                             infer_st_rewrs] >>
     `check_s tvs (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) (st'' with next_uvar := st''.next_uvar + 1).subst`
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) t1`
               by metis_tac [check_t_more4, infer_e_check_t, infer_st_rewrs, DECIDE ``x ≤ x + 1:num``] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) (Infer_Tuvar st''.next_uvar)`
                  by srw_tac[] [check_t_def] >>
     qpat_assum `!t1 t2 st st' tvs. P t1 t2 st st' tvs` match_mp_tac >>
     metis_tac [infer_st_rewrs, check_s_more],
 `check_env (count st''.next_uvar) (opt_bind x (0,t1) env)`
         by (srw_tac[] [opt_bind_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss()) [check_env_bind] >>
             metis_tac [infer_e_check_t, check_env_more, infer_e_next_uvar_mono]) >>
     metis_tac [infer_e_wfs],
 `check_env (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar)
            (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs))) ++ env)`
                 by (srw_tac[] [check_env_merge] >>
                     srw_tac[] [check_env_letrec_lem] >>
                     metis_tac [check_env_more, DECIDE ``x ≤ x + y:num``]) >>
     `check_s tvs (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar) st.subst`
                 by metis_tac [infer_st_rewrs, check_s_more2, DECIDE ``x ≤ x + y:num``] >>
     `check_s tvs (count st'''.next_uvar) st'''.subst`
                 by metis_tac [infer_st_rewrs] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     `check_s tvs (count st'''.next_uvar) st''''.subst`
                 by (match_mp_tac pure_add_constraints_check_s >>
                     qexists_tac `st'''.subst` >>
                     qexists_tac `ZIP (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)),funs_ts)` >>
                     srw_tac[] [EVERY_CONJ, every_shim2, every_zip_snd, every_zip_fst, LENGTH_COUNT_LIST, EVERY_MAP,
                         every_count_list, check_t_def] >|
                     [`st.next_uvar + LENGTH funs ≤ st'''.next_uvar` by metis_tac [infer_st_rewrs, infer_e_next_uvar_mono] >>
                          decide_tac,
                      metis_tac [infer_e_check_t, check_t_more2, arithmeticTheory.ADD_0]]) >>
     `t_wfs st''''.subst` by metis_tac [pure_add_constraints_wfs] >>
     `check_env (count st''''.next_uvar)
            (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs))) ++ env)`
                  by metis_tac [check_env_more, infer_e_next_uvar_mono, infer_st_rewrs] >>
     metis_tac [],
 metis_tac [infer_e_check_t, check_env_more, infer_e_next_uvar_mono, infer_e_wfs],
 PairCases_on `v'` >>
     `t_wfs st''.subst ∧  
      EVERY (λ(x,t). check_t 0 (count st''.next_uvar) t) v'1 ∧
      check_t 0 (count st''.next_uvar) v'0 ∧
      check_env (count st''.next_uvar) env ∧
      check_s tvs (count st''.next_uvar) st''.subst`
             by metis_tac [infer_p_check_t, infer_p_wfs, infer_p_check_s, infer_p_next_uvar_mono,
                           check_env_more] >>
     full_simp_tac(srw_ss()) [] >>
     `check_s tvs (count st''.next_uvar) s` 
                  by metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0, infer_p_next_uvar_mono,
                                check_t_more4] >>
     `check_env (count st''.next_uvar) (MAP (λ(n,t). (n,0,t)) v'1 ++ env)`
              by (srw_tac[] [check_env_merge] >>
                  srw_tac[] [check_env_def, EVERY_MAP, LAMBDA_PROD]) >>
     `t_wfs s` by metis_tac [t_unify_wfs] >>
     `check_t 0 (count st''''.next_uvar) t2' ∧ t_wfs st''''.subst`
                by metis_tac [infer_e_check_t, infer_e_wfs, infer_st_rewrs] >>
     `check_t 0 (count st''.next_uvar) t2 ∧ check_t 0 (count st''.next_uvar) t1`
                by metis_tac [check_t_more4, infer_p_next_uvar_mono] >>
     `check_t 0 (count st''''.next_uvar) t2 ∧ check_t 0 (count st''''.next_uvar) t1`
                by metis_tac [check_t_more4, infer_st_rewrs, infer_e_next_uvar_mono] >>
     `check_s tvs (count st''''.next_uvar) st''''.subst`
                by metis_tac [infer_st_rewrs] >>
     `t_wfs s'` by metis_tac [t_unify_wfs] >>
     `check_s tvs (count st''''.next_uvar) s'` 
                by (match_mp_tac t_unify_check_s >>
                    metis_tac [check_s_more, check_t_more2, arithmeticTheory.ADD_0]) >>
     `check_t 0 (count st''''.next_uvar) t2`
                by metis_tac [check_t_more4, infer_e_next_uvar_mono] >>
     `check_env (count st''''.next_uvar) env` by metis_tac [infer_e_next_uvar_mono, infer_st_rewrs, check_env_more] >>
     qpat_assum `!st''' st''''' tvs'. P st''' st''''' tvs'` match_mp_tac >>
     metis_tac [infer_st_rewrs],
 `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) ((x, (0,Infer_Tuvar st.next_uvar)):: env)`
               by (srw_tac[] [check_env_bind, check_t_def] >>
                   metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
     `check_s tvs (count (st with next_uvar := st.next_uvar + 1).next_uvar) (st with next_uvar := st.next_uvar + 1).subst` 
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `t_wfs (st with next_uvar := st.next_uvar + 1).subst` by srw_tac[] [] >>
     `check_s tvs (count st'''.next_uvar) st'''.subst ∧ t_wfs st'''.subst` 
               by metis_tac [infer_e_wfs]  >>
     `check_env (count st'''.next_uvar) env` 
               by metis_tac [infer_e_next_uvar_mono, check_env_more, infer_st_rewrs, DECIDE ``x ≤ x + 1:num``] >>
     metis_tac []]);

val helper_lemma = Q.prove (
`!l1 l2 n.
  (LENGTH l1 = LENGTH l2) ∧
  check_env (count n) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l1 (MAP (λn. Infer_Tuvar n) l2))
  ⇒
  check_env (count (SUC n)) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l1 (MAP (λn. Infer_Tuvar n) (MAP SUC l2)))`,
induct_on `l1` >>
srw_tac[] [] >>
Cases_on `l2` >>
full_simp_tac(srw_ss()) [check_env_def] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [check_t_def]);

val check_env_letrec = Q.store_thm ("check_env_letrec",
`!l tvs.
  check_env (count (LENGTH l)) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`,
induct_on `l` >>
srw_tac[] [COUNT_LIST_def] >>
srw_tac[] [COUNT_LIST_def, check_env_def] >|
[PairCases_on `h` >>
     srw_tac[] [check_t_def],
 full_simp_tac(srw_ss()) [GSYM check_env_def] >>
     full_simp_tac(srw_ss()) [MAP2_MAP, COUNT_LIST_def] >>
     metis_tac [helper_lemma, LENGTH_COUNT_LIST]]);

val check_build_ctor_tenv = Q.prove (
`!mn cenv l. tenvT_ok tenvT ∧ check_ctor_tenv mn tenvT l ⇒ check_flat_cenv (build_ctor_tenv mn tenvT l)`,
 induct_on `l` >>
 srw_tac[] [EVERY_REVERSE, check_flat_cenv_def, build_ctor_tenv_def, check_ctor_tenv_def]
 >- (PairCases_on `h` >>
     srw_tac[] [EVERY_MAP] >>
     full_simp_tac(srw_ss()) [remove_pair_lem] >>
     full_simp_tac(srw_ss()) [every_shim, EVERY_MAP] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     srw_tac[] [] >>
     match_mp_tac check_freevars_type_name_subst >>
     res_tac >>
     srw_tac[] [])
 >- (full_simp_tac(srw_ss()) [check_flat_cenv_def, build_ctor_tenv_def, check_ctor_tenv_def, EVERY_REVERSE] >>
     `check_dup_ctors l` 
                by (PairCases_on `h` >> metis_tac [check_dup_ctors_cons]) >>
     metis_tac []));

val infer_d_check_helper = Q.prove (
`!l1 l2 s tvs.
  (LENGTH l1 = LENGTH l2) ∧
  EVERY (\n. check_t tvs {} (t_walkstar s (Infer_Tuvar n))) l2
  ⇒
  EVERY (λx. (λ(x,tvs,t). check_t tvs ∅ t) ((λ((f,x,e),t). (f,tvs,t)) x))
    (ZIP (l1, MAP (t_walkstar s) (MAP (λn. Infer_Tuvar n) l2)))`,
Induct_on `l2` >>
srw_tac[] [COUNT_LIST_def, EVERY_MAP] >>
cases_on `l1` >>
full_simp_tac(srw_ss()) [] >>
PairCases_on `h'` >>
srw_tac[] []);

val infer_d_check_s_helper1 = Q.store_thm ("infer_d_check_s_helper1",
`!menv cenv env e t1 st1 p t env2 st2 s.
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env ∧
  (infer_e menv cenv env e init_infer_state = (Success t1, st1)) ∧
  (infer_p cenv p st1 = (Success (t, env2), st2)) ∧
  (t_unify st2.subst t1 t = SOME s)
  ⇒
  check_s 0 (count st2.next_uvar) s`,
srw_tac[] [] >>
full_simp_tac(srw_ss()) [success_eqns, init_state_def] >>
`t_wfs init_infer_state.subst ∧ 
 ((count (init_infer_state:(num|->infer_t) infer_st).next_uvar) = {}) ∧
 check_s 0 (count init_infer_state.next_uvar) init_infer_state.subst`
           by (full_simp_tac(srw_ss()) [init_infer_state_def] >>
               srw_tac[] [t_wfs_def, check_s_def]) >>
`t_wfs st1.subst ∧ t_wfs st2.subst` by metis_tac [infer_p_wfs, infer_e_wfs] >>
`check_t 0 (count st2.next_uvar) t1 ∧
 check_t 0 (count st2.next_uvar) t`
            by metis_tac [infer_p_check_t, infer_e_check_t,
                          check_t_more4, infer_p_next_uvar_mono] >>
 match_mp_tac t_unify_check_s >>
 prove_tac [infer_p_check_s, infer_e_check_s]);

val infer_d_check_s_helper2 = Q.store_thm ("infer_d_check_s_helper2",
`!menv cenv l env funs_ts st1 st2 s.
    (LENGTH funs_ts = LENGTH l) ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env {} env ∧
    infer_funs menv cenv
           (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l
              (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))) ++ env) l
        (init_infer_state with next_uvar := LENGTH l) = (Success funs_ts,st2) ∧
     pure_add_constraints st2.subst
        (ZIP (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)),funs_ts))
        s
 ⇒
 check_s 0 (count st2.next_uvar) s`,
srw_tac[] [] >>
full_simp_tac(srw_ss()) [success_eqns, init_state_def] >>
match_mp_tac pure_add_constraints_check_s >>
`check_env (count (LENGTH l))
           (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l
              (MAP (λn. Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l))) ++ env)`
         by (srw_tac[] [check_env_merge, check_env_letrec_lem] >>
             metis_tac [check_env_more, COUNT_ZERO, DECIDE ``!x. 0 ≤ x:num``]) >>
`t_wfs init_infer_state.subst ∧ check_s 0 {} init_infer_state.subst` by full_simp_tac(srw_ss()) [check_s_def, t_wfs_def, init_infer_state_def] >>
`check_s 0 (count (init_infer_state with next_uvar := LENGTH l).next_uvar) (init_infer_state with next_uvar := LENGTH l).subst`
          by (full_simp_tac(srw_ss()) [] >> metis_tac [check_s_more2, infer_e_wfs, COUNT_ZERO, DECIDE ``!x. 0 ≤ x:num``]) >>
qexists_tac `st2.subst` >>
qexists_tac `(ZIP (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)),funs_ts))` >>
srw_tac[] [] >|
[`t_wfs (init_infer_state with next_uvar := LENGTH l).subst` by srw_tac[] [] >>
     metis_tac [infer_e_wfs],
 srw_tac[] [EVERY_CONJ, every_shim2, every_zip_snd, every_zip_fst, LENGTH_COUNT_LIST, EVERY_MAP,
     every_count_list, check_t_def] >>
     `(init_infer_state with next_uvar := LENGTH l).next_uvar ≤ st2.next_uvar` by metis_tac [infer_e_next_uvar_mono] >|
     [full_simp_tac(srw_ss()) [] >>
          decide_tac,
      imp_res_tac infer_e_check_t >>
          full_simp_tac(srw_ss()) [] >>
          metis_tac [check_env_more]],
 match_mp_tac (hd (tl(tl(tl(CONJUNCTS infer_e_check_s))))) >>
     MAP_EVERY qexists_tac [`menv`, `cenv`, 
                            `(MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l (MAP (λn. Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l))) ++ env)`,
                            `l`,
                            `(init_infer_state with next_uvar := LENGTH l)`,
                            `funs_ts`] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) []]);

val generalise_complete_lemma = Q.prove (
`!tvs ts.
  (∀uv. uv ∈ FDOM (FEMPTY |++ ts) ⇒ ∃tv. (FEMPTY |++ ts) ' uv = tv ∧ tv < tvs)
  ⇒
  (∀uv. uv ∈ FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ⇒ ∃tv. (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ' uv = Infer_Tvar_db tv ∧ tv < tvs)`,
srw_tac[] [FDOM_FUPDATE_LIST, MEM_MAP] >>
PairCases_on `y'` >>
full_simp_tac(srw_ss()) [] >>
`y'0 ∈ FDOM (FEMPTY |++ ts)` 
        by (srw_tac[] [FDOM_FUPDATE_LIST, MEM_MAP] >> metis_tac [FST]) >>
metis_tac [FST, fupdate_list_map]);

val generalise_complete_lemma2 = Q.prove (
`!s ts.
  t_wfs s ∧
  ALL_DISTINCT (MAP FST ts) ∧
  EVERY (\t. t = Infer_Tapp [] TC_unit ∨ ?tvs. t = Infer_Tvar_db tvs) (MAP SND ts) ∧
  DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))
  ⇒
  pure_add_constraints s (MAP (\(uv,t). (Infer_Tuvar uv, t)) ts) (s |++ ts)`,
induct_on `ts` >>
srw_tac[] [pure_add_constraints_def, FUPDATE_LIST_THM] >>
PairCases_on `h` >>
srw_tac[] [pure_add_constraints_def] >>
`t_unify s (Infer_Tuvar h0) h1 = SOME (s |+ (h0,h1))` 
           by (srw_tac[] [t_unify_eqn] >>
               srw_tac[] [Once t_walk_eqn] >>
               srw_tac[] [Once t_vwalk_eqn, FLOOKUP_DEF] >|
               [full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
                    metis_tac [],
                full_simp_tac(srw_ss()) [] >>
                    srw_tac[] [t_walk_eqn, t_ext_s_check_eqn, oc_tvar_db, oc_unit]]) >>
`t_wfs (s |+ (h0,h1))` by metis_tac [t_unify_wfs] >>
qexists_tac `s |+ (h0,h1)` >>
srw_tac[] [] >>
`DISJOINT (FDOM (s |+ (h0,h1))) (FDOM (FEMPTY |++ ts))`
         by (full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
             metis_tac []) >>
metis_tac []);

val infer_subst_var_def = Define `
(infer_subst_var s (Infer_Tuvar n) = 
  case FLOOKUP s n of
    | NONE => Infer_Tuvar n
    | SOME tv => Infer_Tvar_db tv) ∧
(infer_subst_var s t = t)`;

val generalise_complete_lemma4 = Q.prove (
`!s. t_wfs s ⇒
  !t s'. t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') ∧
         ALL_DISTINCT (MAP FST s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s')) ⇒
         infer_subst_var (FEMPTY |++ s') (t_vwalk s t) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') t`,
 strip_tac >>
 strip_tac >>
 imp_res_tac (DISCH_ALL t_vwalk_ind) >>
 pop_assum ho_match_mp_tac >>
 srw_tac[] [] >>
 imp_res_tac t_vwalk_eqn >>
 ONCE_ASM_REWRITE_TAC [] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 full_simp_tac(srw_ss()) [flookup_fupdate_list, infer_subst_var_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [infer_subst_var_def, flookup_fupdate_list] >>
 every_case_tac >>
 full_simp_tac(srw_ss()) [ALOOKUP_FAILS, PROVE [flookup_thm] ``FLOOKUP f x = NONE ⇔ x ∉ FDOM f``] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss()) [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11]
 >- (full_simp_tac(srw_ss()) [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss()) [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss()) [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac []));

val generalise_complete_lemma5 = Q.prove (
`!s. t_wfs s ⇒
  !t s'. t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') ⇒
         ALL_DISTINCT (MAP FST s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s')) ⇒
         infer_subst (FEMPTY |++ s') (t_walkstar s t) = t_walkstar (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') t`,
 strip_tac >>
 strip_tac >>
 imp_res_tac t_walkstar_ind >>
 pop_assum ho_match_mp_tac >>
 srw_tac[] [] >>
 cases_on `t` >>
 srw_tac[] [t_walkstar_eqn, t_walk_eqn, infer_subst_def] >>
 full_simp_tac(srw_ss()) [t_walk_eqn]
 >- (induct_on `l` >>
     srw_tac[] []) >>
 `infer_subst_var (FEMPTY |++ s') (t_vwalk s n) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n`
          by metis_tac [generalise_complete_lemma4] >>
 cases_on `t_vwalk s n` >>
 srw_tac[] [] >>
 cases_on `t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n` >>
 srw_tac[] [] >> 
 full_simp_tac(srw_ss()) [infer_subst_def, infer_subst_var_def] >>
 srw_tac[] [MAP_MAP_o, MAP_EQ_f] >>
 cases_on `FLOOKUP (FEMPTY |++ s') n'` >>
 full_simp_tac(srw_ss()) []);

val fst_lem = Q.prove (
`FST = (\(x,y).x)`,
srw_tac[] [FUN_EQ_THM] >>
PairCases_on `x` >>
srw_tac[] []);

val generalise_complete = Q.store_thm ("generalise_complete",
`!n s l tvs s' ts tvs next_uvar.
  t_wfs s ∧
  check_s 0 (count next_uvar) s ∧
  EVERY (\t. check_t 0 (count next_uvar) t) l ∧
  (generalise_list 0 n FEMPTY (MAP (t_walkstar s) l) = (tvs,s',ts))
  ⇒
  ?ec1 last_sub. 
    (ts = MAP (t_walkstar last_sub) l) ∧
    t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub`,
srw_tac[] [] >>
imp_res_tac generalise_subst_empty >>
srw_tac[] [sub_completion_def] >>
Q.ABBREV_TAC `unconstrained = count next_uvar DIFF (FDOM s ∪ FDOM s')` >>
`?ts. ALL_DISTINCT (MAP FST ts) ∧ s' = FEMPTY |++ ts` by metis_tac [fmap_to_list] >>
srw_tac[] [] >>
`FINITE unconstrained` by metis_tac [FINITE_COUNT, FINITE_DIFF, FINITE_UNION, finite_t_rangevars] >>
`?ts2. ALL_DISTINCT (MAP FST ts2) ∧ FEMPTY |++ ts2 = (FUN_FMAP (\x. Infer_Tapp [] TC_unit) unconstrained)` by metis_tac [fmap_to_list] >>
`DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts2))` 
             by (srw_tac[] [EXTENSION, DISJOINT_DEF] >>
                 Q.UNABBREV_TAC `unconstrained` >>
                 srw_tac[] [] >>
                 CCONTR_TAC >>
                 full_simp_tac(srw_ss()) [] >>
                 full_simp_tac(srw_ss()) []) >>
`DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))` 
             by (srw_tac[] [] >>
                 full_simp_tac(srw_ss()) [MEM_MAP] >>
                 srw_tac[] [EXTENSION, DISJOINT_DEF] >>
                 full_simp_tac(srw_ss()) [] >>
                 metis_tac [t_walkstar_vars_notin]) >>
`t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)` 
      by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)`
             by (srw_tac[] [t_vR_eqn, FUN_EQ_THM] >>
                 every_case_tac >>
                 full_simp_tac(srw_ss()) [flookup_fupdate_list] >>
                 every_case_tac >>
                 full_simp_tac(srw_ss()) [] >>
                 imp_res_tac ALOOKUP_MEM >>
                 full_simp_tac(srw_ss()) [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, t_vars_eqn] >>
                 full_simp_tac(srw_ss()) [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MEM_MAP] >>
                 metis_tac [pair_CASES, FST]) >>
         full_simp_tac(srw_ss()) [t_vars_eqn, t_wfs_eqn]) >>
`t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)` 
      by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
             by (srw_tac[] [t_vR_eqn, FUN_EQ_THM] >>
                 cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) x'` >>
                 srw_tac[] [flookup_update_list_some, flookup_update_list_none] >-
                 full_simp_tac(srw_ss()) [flookup_update_list_none] >>
                 pop_assum mp_tac >>
                 srw_tac[] [flookup_update_list_some] >|
                 [imp_res_tac ALOOKUP_MEM >>
                      pop_assum mp_tac >>
                      srw_tac[] [MAP_REVERSE] >>
                      `x' ∈ FDOM (FEMPTY |++ ts2)` 
                                by metis_tac [MEM_MAP, FDOM_FUPDATE_LIST, IN_UNION, FST, pair_CASES] >>
                      `x' ∉ FDOM s` by (full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s x' = NONE` by metis_tac [FLOOKUP_DEF] >>
                      srw_tac[] [] >>
                      `FLOOKUP (FEMPTY |++ ts2) x' = SOME x''` by srw_tac[] [flookup_update_list_some] >>
                      pop_assum mp_tac >>
                      srw_tac[] [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                      srw_tac[] [FLOOKUP_FUN_FMAP, t_vars_eqn],
                 imp_res_tac ALOOKUP_MEM >>
                      pop_assum mp_tac >>
                      srw_tac[] [MEM_MAP, MAP_REVERSE] >>
                      PairCases_on `y` >>
                      srw_tac[] [] >>
                      `MEM y0 (MAP FST ts)` by (srw_tac[] [MEM_MAP] >> metis_tac [FST]) >>
                      `y0 ∈ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                      `y0 ∉ FDOM s` by (full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s y0 = NONE` by metis_tac [FLOOKUP_DEF] >>
                      srw_tac[] [] >>
                      full_simp_tac(srw_ss()) [] >>
                      `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) y0 = SOME x''` by srw_tac[] [flookup_update_list_some] >>
                      imp_res_tac ALOOKUP_MEM >>
                      full_simp_tac(srw_ss()) [MEM_MAP] >>
                      srw_tac[] [] >>
                      PairCases_on `y'` >>
                      srw_tac[] [] >>
                      srw_tac[] [t_vars_eqn, encode_infer_t_def],
                  srw_tac[] []]) >>
         full_simp_tac(srw_ss()) [t_vars_eqn, t_wfs_eqn]) >>
`count next_uvar ⊆ FDOM (s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2)`
      by (srw_tac[] [FDOM_FUPDATE_LIST, SUBSET_DEF] >>
          CCONTR_TAC >>
          full_simp_tac(srw_ss()) [] >>
          `x ∉ FDOM (FEMPTY |++ ts2)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
          pop_assum mp_tac >>
          srw_tac[] [FLOOKUP_FUN_FMAP] >>
          `x ∉ set (MAP FST ts)` by metis_tac [map_fst] >>
          `x ∉ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
          Q.UNABBREV_TAC `unconstrained` >>
          srw_tac[] []) >>
`DISJOINT (FDOM (FEMPTY |++ ts)) (FDOM (FEMPTY |++ ts2))` 
             by (Q.UNABBREV_TAC `unconstrained` >>
                 srw_tac[] [DISJOINT_DEF, EXTENSION] >>
                 metis_tac []) >>
qexists_tac `(MAP (\(uv,tv). (Infer_Tuvar uv, Infer_Tvar_db tv)) ts) ++ 
             (MAP (\(uv,t). (Infer_Tuvar uv, t)) ts2)` >>
qexists_tac `s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2` >>
srw_tac[] [] >|
[srw_tac[] [MAP_EQ_f, MAP_MAP_o] >>
     `DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts))`
               by (full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, map_fst] >>
                   metis_tac []) >>
     `infer_subst (FEMPTY |++ ts) (t_walkstar s e) = t_walkstar (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) e`
               by metis_tac [generalise_complete_lemma5] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [] >>
     `(t_vars o infer_subst (FEMPTY |++ ts) o t_walkstar s) e = {}`
             by metis_tac [no_vars_lem, MAP_MAP_o] >>
     full_simp_tac(srw_ss()) [combinTheory.o_DEF] >>
     pop_assum mp_tac >>
     srw_tac[] [] >>
     `DISJOINT (FDOM (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) (FDOM (FEMPTY |++ ts2))`
                by (srw_tac[] [FDOM_FUPDATE_LIST, map_fst] >>
                    full_simp_tac(srw_ss()) [FDOM_FUPDATE_LIST]) >>
     metis_tac [no_vars_extend_subst],
 `MAP (λ(uv,tv). (Infer_Tuvar uv,Infer_Tvar_db tv)) ts ++ MAP (λ(uv,t). (Infer_Tuvar uv,t)) ts2
  =
  MAP (λ(uv,t). (Infer_Tuvar uv, t)) (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts ++ ts2)`
            by srw_tac[] [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
     ASM_REWRITE_TAC [GSYM FUPDATE_LIST_APPEND] >>
     match_mp_tac generalise_complete_lemma2 >>
     srw_tac[] [MAP_MAP_o, EVERY_MAP, LAMBDA_PROD, ALL_DISTINCT_APPEND, combinTheory.o_DEF] >|
     [metis_tac [fst_lem],
      `e ∈ FDOM (FEMPTY |++ ts)`
                   by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, fst_lem] >>
          `e ∉ unconstrained`
                   by (Q.UNABBREV_TAC `unconstrained` >>
                       full_simp_tac(srw_ss()) []) >>
          `e ∉ FDOM (FEMPTY |++ ts2)`
                    by metis_tac [FDOM_FMAP] >>
          full_simp_tac(srw_ss()) [FDOM_FUPDATE_LIST],
      srw_tac[] [EVERY_MEM] >>
          PairCases_on `e` >>
          srw_tac[] [],
      srw_tac[] [EVERY_MEM] >>
          PairCases_on `e` >>
          srw_tac[] [] >>
          `FLOOKUP (FEMPTY |++ ts2) e0 = SOME e1` 
                    by (srw_tac[] [flookup_fupdate_list] >>
                        full_case_tac >>
                        full_simp_tac(srw_ss()) [ALOOKUP_FAILS] >>
                        metis_tac [optionTheory.SOME_11,ALOOKUP_ALL_DISTINCT_MEM, MEM_REVERSE, ALL_DISTINCT_REVERSE, REVERSE_REVERSE, MAP_REVERSE]) >>
          pop_assum mp_tac >>
          srw_tac[] [FLOOKUP_FUN_FMAP],
      full_simp_tac(srw_ss()) [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
          srw_tac[] [map_fst] >>
          metis_tac []],
 ONCE_REWRITE_TAC [GSYM COUNT_ZERO] >>
     match_mp_tac t_walkstar_check >>
     srw_tac[] [check_t_def, check_s_def] >>
     `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) uv' = SOME ((s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) ' uv')` 
                    by srw_tac[] [FLOOKUP_DEF] >>
     pop_assum mp_tac >>
     srw_tac[] [flookup_update_list_some] >>
     Q.ABBREV_TAC `last_sub = s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2` >|
     [`FLOOKUP (FEMPTY |++ ts2) uv' = SOME (last_sub ' uv')` by metis_tac [flookup_update_list_some] >>
          pop_assum mp_tac >>
          srw_tac[] [FLOOKUP_FUN_FMAP] >>
          metis_tac [check_t_def, EVERY_DEF],
      `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) uv' = SOME (last_sub ' uv')`
                    by metis_tac [flookup_update_list_some] >>
          `(!uv. uv ∈ FDOM (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ⇒ ∃tv. (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ' uv = Infer_Tvar_db tv ∧ tv < tvs + n)`
                   by metis_tac [generalise_complete_lemma] >>
          full_simp_tac(srw_ss()) [FLOOKUP_DEF] >>
          metis_tac [check_t_def],
      full_simp_tac(srw_ss()) [check_s_def, FLOOKUP_DEF] >>
          metis_tac [check_t_more2, check_t_more5, arithmeticTheory.ADD_0]]]);

val infer_d_check = Q.store_thm ("infer_d_check",
`!mn decls menv cenv env d st1 st2 decls' cenv' env' tenv.
  tenvT_ok tenvT ∧
  infer_d mn decls tenvT menv cenv env d st1 = (Success (decls',tenvT',cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  flat_tenvT_ok tenvT' ∧
  check_flat_cenv cenv' ∧
  check_env {} env'`,
 cases_on `d` >>
 rpt gen_tac >>
 strip_tac >>
 `?mdecls tdecls edecls. decls = (mdecls,tdecls,edecls)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss()) [infer_d_def, success_eqns] >>
 full_simp_tac(srw_ss()) []
 >- (`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     `?tvs s ts. generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env'')) = (tvs,s,ts)`
                 by (cases_on `generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env''))` >>
                     srw_tac[] [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     full_simp_tac(srw_ss()) [METIS_PROVE [] ``!x. (x = 0:num ∨ is_value e) = (x<>0 ⇒ is_value e)``] >>
     srw_tac[] [flat_tenvT_ok_def] >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [check_flat_cenv_def, check_env_def] >>
     `st''.next_uvar = 0` by (full_simp_tac(srw_ss()) [init_state_def, init_infer_state_def] >> srw_tac[] []) >>
     full_simp_tac(srw_ss()) [FEVERY_FEMPTY] >>
     imp_res_tac infer_p_check_t >>
     full_simp_tac(srw_ss()) [every_shim, init_state_def] >>
     `t_wfs init_infer_state.subst` by srw_tac[] [t_wfs_def, init_infer_state_def] >>
     `t_wfs s` by metis_tac [t_unify_wfs, infer_e_wfs, infer_p_wfs] >>
     `?ec1 last_sub.
       (ts = MAP (t_walkstar last_sub) (MAP SND env'')) ∧
       t_wfs last_sub ∧
       sub_completion tvs st''''.next_uvar s ec1 last_sub`
                  by metis_tac [arithmeticTheory.ADD_0, generalise_complete, infer_d_check_s_helper1] >>
     srw_tac[] [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP] >>
     full_simp_tac(srw_ss()) [EVERY_MAP] >>
     full_simp_tac(srw_ss()) [sub_completion_def] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     srw_tac[] [] >>
     res_tac >>
     match_mp_tac (hd (CONJUNCTS check_t_walkstar)) >>
     metis_tac [check_t_more5])
 >- (full_simp_tac(srw_ss()) [success_eqns] >>
     `?tvs s ts. generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l)))) = (tvs,s,ts)`
                 by (cases_on `generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l))))` >>
                     srw_tac[] [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [check_flat_cenv_def, flat_tenvT_ok_def] >>
     `EVERY (\t. check_t 0 (count st''''.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))`
                 by (srw_tac[] [EVERY_MAP, check_t_def] >>
                     srw_tac[] [EVERY_MEM, MEM_COUNT_LIST] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     full_simp_tac(srw_ss()) [] >>
                     decide_tac) >>
     `st'''.next_uvar = 0` by (full_simp_tac(srw_ss()) [init_state_def, init_infer_state_def] >> srw_tac[] []) >>
     full_simp_tac(srw_ss()) [init_state_def, FEVERY_FEMPTY] >>
     `t_wfs (st''' with next_uvar := LENGTH l).subst` by srw_tac[] [t_wfs_def, init_infer_state_def] >>
     `t_wfs st'''''.subst` by metis_tac [infer_e_wfs, pure_add_constraints_wfs] >>
     `?ec1 last_sub. 
        (ts = MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))) ∧
        t_wfs last_sub ∧
        sub_completion tvs st''''.next_uvar st'''''.subst ec1 last_sub`
                 by metis_tac [arithmeticTheory.ADD_0, generalise_complete, infer_d_check_s_helper2, LENGTH_COUNT_LIST] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [sub_completion_def] >>
     `LENGTH l = LENGTH (MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`
             by metis_tac [LENGTH_COUNT_LIST, LENGTH_MAP] >>
     srw_tac[] [check_env_def, MAP2_ZIP, EVERY_MAP] >>
     match_mp_tac infer_d_check_helper >>
     srw_tac[] [LENGTH_COUNT_LIST] >>
     full_simp_tac(srw_ss()) [LENGTH_COUNT_LIST, every_count_list] >>
     srw_tac[] [] >>
     imp_res_tac infer_e_next_uvar_mono >>
     full_simp_tac(srw_ss()) [] >>
     `n < st''''.next_uvar` by decide_tac >>
     `n ∈ FDOM last_sub` by full_simp_tac(srw_ss()) [SUBSET_DEF] >>
     metis_tac [])
 >- (every_case_tac >>
     full_simp_tac(srw_ss()) [success_eqns, flookup_update_list_some] >>
     srw_tac[] [check_env_def]
     >- (full_simp_tac(srw_ss()) [flat_tenvT_ok_def, EVERY_MAP, EVERY_MEM] >>
         srw_tac[] [FEVERY_ALL_FLOOKUP, flookup_update_list_some] >>
         imp_res_tac ALOOKUP_MEM >>
         PairCases_on `v` >>
         full_simp_tac(srw_ss()) [EVERY_MAP, EVERY_MEM, MEM_MAP] >>
         PairCases_on `y` >>
         full_simp_tac(srw_ss()) [] >>
         srw_tac[] [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
     match_mp_tac check_build_ctor_tenv >>
     srw_tac[] [EVERY_MAP, check_freevars_def, EVERY_MEM] >>
     match_mp_tac tenvT_ok_merge >>
     srw_tac[] [tenvT_ok_def, FEVERY_FEMPTY] >>
     srw_tac[] [flat_tenvT_ok_def, FEVERY_ALL_FLOOKUP, flookup_update_list_some] >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [EVERY_MAP, EVERY_MEM, MEM_MAP] >>
     PairCases_on `y` >>
     full_simp_tac(srw_ss()) [] >>
     srw_tac[] [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (srw_tac[] [check_flat_cenv_def, check_env_def, flat_tenvT_ok_def, FEVERY_FUPDATE, FEVERY_FEMPTY] >>
     match_mp_tac check_freevars_type_name_subst >>
     full_simp_tac(srw_ss())[])
 >- (every_case_tac >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [check_env_def, flat_tenvT_ok_def, check_flat_cenv_def, check_exn_tenv_def,
         FEVERY_FEMPTY, EVERY_MAP, FEVERY_DEF] >>
     full_simp_tac(srw_ss()) [EVERY_MEM] >>
     srw_tac[] [] >>
     match_mp_tac check_freevars_type_name_subst >>
     full_simp_tac(srw_ss())[]));

val infer_ds_check = Q.store_thm ("infer_ds_check",
`!mn decls tenvT menv cenv env ds st1 st2 decls' tenvT' cenv' env' tenv.
  infer_ds mn decls tenvT menv cenv env ds st1 = (Success (decls', tenvT', cenv',env'), st2) ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  flat_tenvT_ok tenvT' ∧
  check_flat_cenv cenv' ∧
  check_env {} env'`,
 induct_on `ds` >>
 srw_tac[] [infer_ds_def, success_eqns]
 >- srw_tac[] [flat_tenvT_ok_def, FEVERY_FEMPTY]
 >- srw_tac[] [check_flat_cenv_def]
 >- srw_tac[] [check_env_def] >>
 `?decls'' tenvT'' cenv'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss()) [success_eqns] >>
 `?decls''' tenvT''' cenv''' env'''. v'' = (decls''',tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss()) [success_eqns] >>
 srw_tac[] [] >>
 `flat_tenvT_ok tenvT'' ∧ check_env {} env'' ∧ check_flat_cenv cenv''` by metis_tac [infer_d_check] >>
 `check_env {} (env'' ++ env) ∧ check_cenv (merge_alist_mod_env ([],cenv'') cenv)` 
            by (full_simp_tac(srw_ss()) [check_env_def, check_cenv_def] >>
                PairCases_on `cenv` >>
                full_simp_tac(srw_ss()) [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def]) >>
 `tenvT_ok (merge_mod_env (FEMPTY,tenvT'') tenvT)`
        by (match_mp_tac tenvT_ok_merge >>
            srw_tac[] [tenvT_ok_def, FEVERY_FEMPTY]) >>
 `check_env {} env''' ∧ flat_tenvT_ok tenvT''' ∧ check_flat_cenv cenv'''` by metis_tac [] >>
 full_simp_tac(srw_ss()) [check_flat_cenv_def, check_env_def, flat_tenvT_ok_def, fevery_funion]);

val check_lem = Q.prove (
`(!t fvs1 fvs2.
  check_t (LENGTH (nub fvs1)) ∅ (infer_type_subst (ZIP (nub fvs1, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs1))))) t)
  ⇒
  check_t (LENGTH (nub (fvs1 ++ fvs2))) ∅ (infer_type_subst (ZIP (nub (fvs1 ++ fvs2), MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub (fvs1 ++ fvs2)))))) t)) ∧
(!ts fvs1 fvs2.
  EVERY (λt.  check_t (LENGTH (nub fvs1)) ∅ (infer_type_subst (ZIP (nub fvs1, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs1))))) t)) ts
  ⇒
  EVERY (λt.  check_t (LENGTH (nub (fvs1 ++ fvs2))) ∅ (infer_type_subst (ZIP (nub (fvs1 ++ fvs2), MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub (fvs1 ++ fvs2)))))) t)) ts)`,
Induct >>
srw_tac[] [check_t_def, infer_type_subst_def, EVERY_MAP] >>
every_case_tac >>
full_simp_tac (srw_ss()++ARITH_ss) [check_t_def, length_nub_append] >|
[imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     srw_tac[] [] >>
     decide_tac,
 imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST, length_nub_append] >>
     srw_tac[] [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def],
 imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST, length_nub_append] >>
     srw_tac[] [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def]]);

val check_lem2 = Q.prove (
`(!t fvs1 fvs2.
  check_t (LENGTH (nub fvs2)) ∅ (infer_type_subst (ZIP (nub fvs2, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs2))))) t)
  ⇒
  check_t (LENGTH (nub (fvs1 ++ fvs2))) ∅ (infer_type_subst (ZIP (nub (fvs1 ++ fvs2), MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub (fvs1 ++ fvs2)))))) t)) ∧
(!ts fvs1 fvs2.
  EVERY (λt.  check_t (LENGTH (nub fvs2)) ∅ (infer_type_subst (ZIP (nub fvs2, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs2))))) t)) ts
  ⇒
  EVERY (λt.  check_t (LENGTH (nub (fvs1 ++ fvs2))) ∅ (infer_type_subst (ZIP (nub (fvs1 ++ fvs2), MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub (fvs1 ++ fvs2)))))) t)) ts)`,
Induct >>
srw_tac[] [check_t_def, infer_type_subst_def, EVERY_MAP] >>
every_case_tac >>
full_simp_tac (srw_ss()++ARITH_ss) [check_t_def, nub_append] >|
[imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     srw_tac[] [] >>
     decide_tac,
 imp_res_tac ALOOKUP_MEM >>
     `LENGTH (nub (FILTER (λx. x ∉ set fvs2) fvs1) ++ nub fvs2) =
      LENGTH (nub fvs2) + LENGTH (nub (FILTER (\x.x ∉ set fvs2) fvs1))`
              by metis_tac [LENGTH_APPEND, arithmeticTheory.ADD_COMM] >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     srw_tac[] [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def],
 imp_res_tac ALOOKUP_MEM >>
     `LENGTH (nub (FILTER (λx. x ∉ set fvs2) fvs1) ++ nub fvs2) =
      LENGTH (nub fvs2) + LENGTH (nub (FILTER (\x.x ∉ set fvs2) fvs1))`
              by metis_tac [LENGTH_APPEND, arithmeticTheory.ADD_COMM] >>
     full_simp_tac(srw_ss()) [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     srw_tac[] [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def]]);

val count_list_one = Q.prove (
`COUNT_LIST 1 = [0]`,
metis_tac [COUNT_LIST_def, MAP, DECIDE ``1 = SUC 0``]);

val t_to_freevars_check2 = Q.prove (
`(!t st fvs st'.
   (t_to_freevars t (st:'a) = (Success fvs, st'))
   ⇒
   check_t (LENGTH (nub fvs)) {}
           (infer_type_subst (ZIP (nub fvs, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs))))) t)) ∧
 (!ts st fvs st'.
   (ts_to_freevars ts (st:'a) = (Success fvs, st'))
   ⇒
   EVERY (\t. check_t (LENGTH (nub fvs)) {} (infer_type_subst (ZIP (nub fvs, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs))))) t)) ts)`,
Induct >>
srw_tac[] [t_to_freevars_def, success_eqns, check_t_def, infer_type_subst_def] >>
srw_tac[] [EVERY_MAP, nub_def, count_list_one, check_t_def] >>
metis_tac [check_lem, check_lem2]);

val check_specs_check = Q.store_thm ("check_specs_check",
`!mn orig_tenvT mdecls tdecls edecls tenvT cenv env specs st decls' tenvT' cenv' env' st'.
  tenvT_ok orig_tenvT ∧
  flat_tenvT_ok tenvT ∧
  check_flat_cenv cenv ∧
  check_env {} env ∧
  (check_specs mn orig_tenvT (mdecls,tdecls,edecls) tenvT cenv env specs st = (Success (decls',tenvT',cenv',env'), st'))
  ⇒
  flat_tenvT_ok tenvT' ∧
  check_flat_cenv cenv' ∧
  check_env {} env'`,
 ho_match_mp_tac check_specs_ind >>
 STRIP_TAC >>
 REPEAT GEN_TAC >-
 (srw_tac[] [check_specs_def, success_eqns] >>
  metis_tac []) >>
 REPEAT CONJ_TAC >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
 full_simp_tac(srw_ss()) [check_specs_def, success_eqns, check_env_bind] 
 >- metis_tac [t_to_freevars_check2]
 >- (rpt gen_tac >>
     strip_tac >>
     FIRST_X_ASSUM match_mp_tac >>
     srw_tac[] [] >>
     qabbrev_tac `new_tenvT = FEMPTY |++ MAP (λ(tvs,tn,ctors). (tn,tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn)))) tdefs` >>
     `flat_tenvT_ok (FUNION new_tenvT tenvT')`
          by (full_simp_tac(srw_ss()) [flat_tenvT_ok_def] >>
              unabbrev_all_tac >>
              match_mp_tac fevery_funion >>
              srw_tac[] [flookup_fupdate_list, FEVERY_ALL_FLOOKUP] >>
              full_case_tac >>
              full_simp_tac(srw_ss()) [] >>
              imp_res_tac ALOOKUP_MEM >>
              full_simp_tac(srw_ss()) [MEM_MAP] >>
              PairCases_on `y` >>
              full_simp_tac(srw_ss()) [] >>
              srw_tac[] [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
     `tenvT_ok (merge_mod_env (FEMPTY,new_tenvT) tenvT)`
          by (match_mp_tac tenvT_ok_merge >>
              full_simp_tac(srw_ss()) [tenvT_ok_def, flat_tenvT_ok_def] >>
              unabbrev_all_tac >>
              srw_tac[] [FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
              full_case_tac >>
              full_simp_tac(srw_ss()) [] >>
              imp_res_tac ALOOKUP_MEM >>
              full_simp_tac(srw_ss()) [MEM_MAP] >>
              PairCases_on `y` >>
              full_simp_tac(srw_ss()) [] >>
              srw_tac[] [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
     MAP_EVERY qexists_tac [`new_tenvT`, `MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs`,
                        `(merge_mod_env (FEMPTY,new_tenvT) tenvT)`, `st`,
                        `decls'`, `st'`] >>
     srw_tac[] [] >>
     full_simp_tac(srw_ss()) [check_flat_cenv_def] >>
     full_simp_tac(srw_ss()) [GSYM check_flat_cenv_def] >>
     match_mp_tac check_build_ctor_tenv >>
     srw_tac[] [])
 >- (rpt gen_tac >>
     strip_tac >>
     FIRST_X_ASSUM match_mp_tac >>
     srw_tac[] [GSYM PULL_EXISTS] >>
     qexists_tac `(tn,tvs,type_name_subst tenvT t)` >>
     srw_tac[] []
     >- (match_mp_tac tenvT_ok_merge >>
         srw_tac[] [tenvT_ok_def, flat_tenvT_ok_def, FEVERY_FUPDATE, FEVERY_FEMPTY] >>
         match_mp_tac check_freevars_type_name_subst >>
         srw_tac[] [])
     >- (full_simp_tac(srw_ss()) [flat_tenvT_ok_def, check_freevars_def, EVERY_MAP, EVERY_MEM, FEVERY_FEMPTY, FEVERY_FUPDATE] >>
         srw_tac[] []
         >- (match_mp_tac check_freevars_type_name_subst >>
             srw_tac[] [])
         >- metis_tac [fevery_to_drestrict])
     >- metis_tac [])
 >- (full_simp_tac(srw_ss()) [check_flat_cenv_def, check_exn_tenv_def,
         tenvT_ok_merge, tenvT_ok_def, flat_tenvT_ok_def, FEVERY_FUPDATE] >>
     full_simp_tac(srw_ss())[EVERY_MAP,EVERY_MEM]>> srw_tac[][]>>
     metis_tac [check_freevars_type_name_subst])
 >- (rpt gen_tac >>
     strip_tac >>
     FIRST_X_ASSUM match_mp_tac >>
     srw_tac[] [GSYM PULL_EXISTS] >>
     qexists_tac `(tn,tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn)))` >>
     srw_tac[] []
     >- (match_mp_tac tenvT_ok_merge >>
         srw_tac[] [tenvT_ok_def, flat_tenvT_ok_def, check_freevars_def,
             EVERY_MAP, EVERY_MEM, FEVERY_FUPDATE, FEVERY_FEMPTY])
     >- (full_simp_tac(srw_ss()) [flat_tenvT_ok_def, check_freevars_def, EVERY_MAP, EVERY_MEM, FEVERY_FUPDATE, FEVERY_FEMPTY] >>
         metis_tac [fevery_to_drestrict])
     >- metis_tac []));

val infer_top_invariant = Q.store_thm ("infer_top_invariant",
`!decls tenvT menv cenv env top st1 decls' tenvT' menv' cenv' env' st2.
  (infer_top decls tenvT menv cenv env top st1 = (Success (decls', tenvT', menv', cenv', env'), st2)) ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  tenvT_ok tenvT' ∧
  check_menv menv' ∧
  check_cenv cenv' ∧
  check_env {} env'`,
 rpt gen_tac >>
 `?mdecls tdecls edecls. decls = (mdecls,tdecls,edecls)` by metis_tac [pair_CASES] >>
 cases_on `top`
 >- (cases_on `o'`
     >- (srw_tac[] [infer_top_def, success_eqns] >>
         `?decls'' tenvT'' cenv'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss()) [success_eqns] >>
         `?mdecls''' tdecls''' edecls''' tenvT''' cenv''' env'''. v'' = ((mdecls''',tdecls''',edecls'''),tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss()) [success_eqns] >>
         full_simp_tac(srw_ss()) [check_signature_def, success_eqns] >>
         srw_tac[] [] >>
         `flat_tenvT_ok tenvT'' ∧ check_flat_cenv cenv'' ∧ check_env {} env''` by metis_tac [infer_ds_check] >>
         srw_tac[] [check_menv_def, check_env_def] >>
         full_simp_tac(srw_ss()) [check_env_def, check_cenv_def, check_flat_cenv_def, tenvT_ok_def,
             flat_tenvT_ok_def, FEVERY_FEMPTY, FEVERY_FUPDATE])
     >- (full_simp_tac(srw_ss()) [infer_top_def, success_eqns] >>
         strip_tac >>
         `?decls'' tenvT'' cenv'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss()) [success_eqns] >>
         `?mdecls''' tdecls''' edecls''' tenvT''' cenv''' env'''. v'' = ((mdecls''',tdecls''',edecls'''),tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss()) [success_eqns] >>
         full_simp_tac(srw_ss()) [check_signature_def, success_eqns] >>
         `?decls'''' tenvT'''' cenv'''' env''''. v''' = (decls'''',tenvT'''',cenv'''',env'''')` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss()) [success_eqns] >>
         `flat_tenvT_ok (FEMPTY:flat_tenvT) ∧ check_flat_cenv [] ∧ check_env {} ([]:(tvarN, num # infer_t) alist)`
                   by srw_tac[] [check_env_def, check_flat_cenv_def, flat_tenvT_ok_def, FEVERY_FEMPTY] >>
         `flat_tenvT_ok tenvT''' ∧ check_flat_cenv cenv''' ∧ check_env {} env'''` by metis_tac [check_specs_check] >>
         srw_tac[] [check_menv_def, check_env_def] >>
         full_simp_tac(srw_ss()) [check_env_def, check_cenv_def, tenvT_ok_def, FEVERY_FEMPTY, FEVERY_FUPDATE]))
 >- (srw_tac[] [infer_top_def, success_eqns] >>
     PairCases_on `v'` >>
     full_simp_tac(srw_ss()) [success_eqns] >>
     srw_tac[] [] >>
     TRY(srw_tac[][check_menv_def, FEVERY_FEMPTY]>>NO_TAC)>>
     full_simp_tac(srw_ss()) [check_cenv_def, check_flat_cenv_def, tenvT_ok_def, FEVERY_FEMPTY] >>
     metis_tac [infer_d_check, check_flat_cenv_def]));


(* ---------- Converting infer types and envs to type system ones ---------- *)

val convert_t_def = tDefine "convert_t" `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`
(WF_REL_TAC `measure infer_t_size` >>
 srw_tac[] [] >>
 induct_on `ts` >>
 srw_tac[] [infer_tTheory.infer_t_size_def] >>
 res_tac >>
 decide_tac);

val convert_menv_def = Define `
convert_menv menv =
  MAP (\(x,(tvs,t)). (x,(tvs,convert_t t))) o_f menv`;

val convert_env_def = Define `
convert_env s env = MAP (\(x,t). (x, convert_t (t_walkstar s t))) env`;

val convert_decls_def = Define `
convert_decls (mdecls,tdecls,edecls) = (set mdecls,set tdecls,set edecls)`;

val convert_append_decls = Q.store_thm ("convert_append_decls",
`!decls1 decls2. convert_decls (append_decls decls1 decls2) = union_decls (convert_decls decls1) (convert_decls decls2)`,
 srw_tac[] [] >>
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 srw_tac[] [convert_decls_def, append_decls_def, union_decls_def]);

val check_convert_freevars = Q.store_thm ("check_convert_freevars",
`(!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))`,
ho_match_mp_tac check_t_ind >>
srw_tac[] [check_freevars_def, check_t_def, convert_t_def] >>
full_simp_tac(srw_ss()) [EVERY_MEM, MEM_MAP] >>
metis_tac []);

val check_t_to_check_freevars = Q.store_thm ("check_t_to_check_freevars",
`!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)`,
ho_match_mp_tac check_t_ind >>
srw_tac[] [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
full_simp_tac(srw_ss()) [EVERY_MEM]);

val convert_inc = Q.store_thm ("convert_inc",
`!t tvs tvs'.
  check_t tvs' {} t
  ⇒
  (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac[] [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
induct_on `ts` >>
full_simp_tac(srw_ss()) [] >>
metis_tac []);

val infer_t_induction = infer_tTheory.infer_t_induction;

val db_subst_infer_subst_swap = Q.store_thm ("db_subst_infer_subst_swap",
`(!t s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  check_t tvs (FDOM s) t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
    (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  EVERY (\t. check_t tvs (FDOM s) t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
       convert_t o 
       t_walkstar (infer_deBruijn_inc tvs o_f s))
      ts))`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST] >|
[`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     full_simp_tac(srw_ss()) [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def,
         LENGTH_COUNT_LIST] >>
     full_simp_tac(srw_ss()) [LENGTH_MAP, el_map_count, EL_COUNT_LIST],
 `t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     full_simp_tac(srw_ss()) [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def, MAP_MAP_o, 
         combinTheory.o_DEF] >>
     metis_tac [],
 res_tac >>
     imp_res_tac convert_inc >>
     srw_tac[] [walkstar_inc2] >>
     metis_tac [subst_inc_cancel, arithmeticTheory.ADD,
                deBruijn_inc0,
                LENGTH_COUNT_LIST, LENGTH_MAP],
 metis_tac [],
 metis_tac []]);

val inc_convert_t = Q.store_thm ("inc_convert_t",
`(!t tvs' tvs. check_t tvs' {} t ⇒ (deBruijn_inc tvs' tvs (convert_t t) = convert_t t)) ∧
 (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ⇒ (MAP (deBruijn_inc tvs' tvs o convert_t) ts = MAP convert_t ts))`,
ho_match_mp_tac infer_t_induction >>
srw_tac[] [check_t_def, convert_t_def, deBruijn_inc_def] >>
metis_tac [MAP_MAP_o]);

val convert_t_subst = Q.store_thm ("convert_t_subst",
`(!t tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    check_freevars 0 tvs t ⇒
    convert_t (infer_type_subst (ZIP (tvs,ts')) t) = 
    type_subst (alist_to_fmap (ZIP (tvs, MAP convert_t ts'))) t) ∧
 (!ts tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    EVERY (check_freevars 0 tvs) ts ⇒
    MAP convert_t (MAP (infer_type_subst (ZIP (tvs,ts'))) ts) = 
    MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP convert_t ts')))) ts)`,
ho_match_mp_tac t_induction >>
srw_tac[] [check_freevars_def, convert_t_def, type_subst_def, infer_type_subst_def] >|
[full_case_tac >>
     full_case_tac >>
     full_simp_tac(srw_ss()) [ALOOKUP_FAILS] >>
     imp_res_tac ALOOKUP_MEM >>
     REPEAT (pop_assum mp_tac) >>
     srw_tac[] [MAP_ZIP] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`tvs`,`tvs`) >>
     induct_on `ts'` >>
     srw_tac[] [] >>
     cases_on `tvs` >>
     full_simp_tac(srw_ss()) [] >>
     metis_tac [optionTheory.SOME_11],
 metis_tac []]);

val sub_completion_wfs = Q.store_thm ("sub_completion_wfs",
`!n uvars s1 ts s2.
  t_wfs s1 ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  t_wfs s2`,
srw_tac[] [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
srw_tac[] [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

val check_cenv_tenvC_ok = Q.store_thm ("check_cenv_tenvC_ok",
`!cenv. tenvC_ok cenv = check_cenv cenv`,
 srw_tac[] [] >>
 PairCases_on `cenv` >>
 srw_tac[] [typeSoundInvariantsTheory.tenvC_ok_def, check_cenv_def,
     check_flat_cenv_def,typeSoundInvariantsTheory.flat_tenvC_ok_def] >>
 srw_tac[] [EVERY_MEM, LAMBDA_PROD]);

val convert_env2_def = Define `
convert_env2 env = MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env`;

(* ---------- tenv_inv, the invariant relating inference and type system * environments ---------- *)

(*Soundness invariant
Everything in the inferencer env is also in the type system env

1) If we are inside an expresesion, then their tvs is just 0 and the
   type system type is just the walk of the inferencer type

2) Else,
  the type system type scheme generalizes the inferencer's type scheme
*)
val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
   (ALOOKUP env x = SOME (tvs,t)) ⇒
    ∃tvs' t'.
    lookup_tenv x 0 tenv = SOME(tvs',t') ∧
    if check_t tvs {} t
    then
      (check_freevars tvs' [] t') ∧
      ∃subst.
        LENGTH subst = tvs' ∧
        EVERY (check_freevars tvs []) subst ∧ 
        deBruijn_subst 0 subst t' = convert_t t 
    else
      (*∃n. check_freevars n [] t') ∧ *)
      tvs = 0 ∧ tvs' = 0 ∧ 
      t' = convert_t (t_walkstar s t))`

val tenv_inv_empty_to = Q.store_thm ("tenv_inv_empty_to",
`!s env tenv.
  t_wfs s ∧ check_env {} env ∧ tenv_inv FEMPTY env tenv 
  ⇒ 
  tenv_inv s env tenv`,
induct_on `env` >>
srw_tac[] [tenv_inv_def] >>
imp_res_tac check_env_lookup >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [] >>
cases_on `h0 = x` >>
full_simp_tac(srw_ss()) [] >>
srw_tac[] [GSYM check_t_subst] >>
metis_tac [t_walkstar_FEMPTY]);

(*
val tenv_inv_extend = Q.store_thm ("tenv_inv_extend",
`!s x tvs t env t' tenv.
  t_wfs s ∧ 
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,tvs,t)::env) (bind_tenv x tvs (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)) tenv)`,
srw_tac[] [tenv_inv_def] >>
every_case_tac >>
srw_tac[] [] >>
srw_tac[] [lookup_tenv_def, bind_tenv_def, deBruijn_inc0] >>
imp_res_tac inc_wfs>>
full_simp_tac(srw_ss())[t_walkstar_no_vars]
metis_tac []);
*)
val tenv_inv_extend0 = Q.store_thm ("tenv_inv_extend0",
`!s x t env tenv.
  t_wfs s ∧ 
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,0,t)::env) (bind_tenv x 0 (convert_t (t_walkstar s t)) tenv)`,
  srw_tac[] [tenv_inv_def] >>Cases_on`x=x'`>>full_simp_tac(srw_ss())[lookup_tenv_def,bind_tenv_def,num_tvs_def]>>
  IF_CASES_TAC>-
    (imp_res_tac t_walkstar_no_vars>>full_simp_tac(srw_ss())[]>>
    imp_res_tac check_t_to_check_freevars>>
    qpat_assum`0=tvs` (SUBST_ALL_TAC o SYM)>>
    full_simp_tac(srw_ss())[deBruijn_inc0]>>
    qexists_tac`[]`>>full_simp_tac(srw_ss())[deBruijn_subst_def]>>
    imp_res_tac deBruijn_subst_id>>
    full_simp_tac(srw_ss())[COUNT_LIST_def])
  >>
    metis_tac[deBruijn_inc0])

val tenv_inv_extend_tvar_empty_subst = Q.store_thm ("tenv_inv_extend_tvar_empty_subst",
`!env tvs tenv.
  check_env {} env ∧ tenv_inv FEMPTY env tenv ⇒ tenv_inv FEMPTY env (bind_tvar tvs tenv)`,
  induct_on `env` >>
  full_simp_tac(srw_ss()) [tenv_inv_def] >>
  srw_tac[] [] >>
  PairCases_on `h` >>
  srw_tac[] [bind_tvar_def, lookup_tenv_def] >>
  full_simp_tac(srw_ss()) [t_walkstar_FEMPTY] >>
  res_tac >>
  imp_res_tac lookup_tenv_inc >>
  full_simp_tac(srw_ss())[]>>
  reverse (Cases_on`h0=x`)>>full_simp_tac(srw_ss())[]
  >-
    (IF_CASES_TAC>>full_simp_tac(srw_ss())[deBruijn_inc0,num_tvs_def]
    >-
      (full_simp_tac(srw_ss())[nil_deBruijn_inc]>>
      metis_tac[])
    >>
    (full_simp_tac(srw_ss())[check_env_def,deBruijn_inc_def,EVERY_MEM]>>
    `MEM (x,0,t) env` by metis_tac[ALOOKUP_MEM]>>
    res_tac>>full_simp_tac(srw_ss())[]>>
    metis_tac[]))
  >>
    full_simp_tac(srw_ss())[check_env_def]>>rfs[nil_deBruijn_inc,num_tvs_def]>>
    metis_tac[])

val tenv_inv_letrec_merge = Q.store_thm ("tenv_inv_letrec_merge",
`!funs tenv' env tenv st s.
  t_wfs s ∧ 
  tenv_inv s env tenv 
  ⇒
  tenv_inv s (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs))) ++ env)
             (bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))) tenv)`,
  induct_on `funs` >>
  srw_tac[] [COUNT_LIST_def, bind_var_list_def] >>
  PairCases_on `h` >>
  srw_tac[] [bind_var_list_def] >>
  match_mp_tac tenv_inv_extend0 >>
  full_simp_tac(srw_ss()) [] >>
  srw_tac[] [check_t_def] >>
  res_tac >>
  pop_assum (mp_tac o Q.SPEC `st with next_uvar := st.next_uvar + 1`) >>
  strip_tac >>
  full_simp_tac(srw_ss()) [] >>
  metis_tac [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]);

val tenv_inv_merge = Q.store_thm ("tenv_inv_merge",
`!s x uv env env' tenv. 
  t_wfs s ∧ 
  tenv_inv s env tenv
  ⇒
  tenv_inv s (MAP (λ(n,t). (n,0,t)) env' ++ env) (bind_var_list 0 (convert_env s env') tenv)`,
  induct_on `env'` >>
  srw_tac[] [convert_env_def, bind_var_list_def] >>
  res_tac >>
  full_simp_tac(srw_ss()) [tenv_inv_def] >>
  srw_tac[] [] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss()) [] >>
  cases_on `h0 = x` >>
  full_simp_tac(srw_ss()) [] >>
  srw_tac[] [bind_var_list_def, bind_tenv_def, lookup_tenv_def,
      deBruijn_inc0, infer_deBruijn_inc0_id, o_f_id]
  >-
    metis_tac[t_walkstar_no_vars,check_t_to_check_freevars]
  >-
    (qexists_tac`[]`>>full_simp_tac(srw_ss())[deBruijn_subst_def]>>
    imp_res_tac check_t_to_check_freevars>>
    imp_res_tac deBruijn_subst_id>>
    full_simp_tac(srw_ss())[COUNT_LIST_def]>>
    metis_tac[t_walkstar_no_vars])
  >>
    res_tac>>
    full_simp_tac(srw_ss())[convert_env_def,num_tvs_def])

(*
val tenv_inv_merge2 = Q.store_thm ("tenv_inv_merge2",
`!env tenv env'' s tvs.
  tenv_inv FEMPTY env tenv 
  ⇒
  tenv_inv FEMPTY
    (MAP (λx. (FST x,tvs,t_walkstar s (SND x))) env'' ++ env)
    (bind_var_list2 (MAP (λx. (FST x,tvs, convert_t (t_walkstar s (SND x)))) env'') tenv)`,
induct_on `env''` >>
srw_tac[] [bind_var_list2_def] >>
PairCases_on `h` >>
srw_tac[] [bind_var_list2_def] >>
res_tac >>
full_simp_tac(srw_ss()) [tenv_inv_def, bind_tenv_def, lookup_tenv_def] >>
srw_tac[] [deBruijn_inc0, t_walkstar_FEMPTY] >>
metis_tac [t_walkstar_FEMPTY]);

val tenv_inv_merge3 = Q.store_thm ("tenv_inv_merge3",
`!l l' env tenv s tvs.
(LENGTH l = LENGTH l') ∧
tenv_inv FEMPTY env tenv
⇒
tenv_inv FEMPTY
     (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
        (MAP (λx. t_walkstar s (Infer_Tuvar x))
           l') ++ env)
  (bind_var_list2
     (MAP (λ(x,tvs,t). (x,tvs,convert_t t))
        (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
           (MAP (λx. t_walkstar s (Infer_Tuvar x))
              l'))) tenv)`,
induct_on `l` >>
srw_tac[] [] >>
cases_on `l'` >>
srw_tac[] [bind_var_list2_def] >>
full_simp_tac(srw_ss()) [] >>
PairCases_on `h` >>
full_simp_tac(srw_ss()) [bind_var_list2_def] >>
full_simp_tac(srw_ss()) [tenv_inv_def, bind_tenv_def, lookup_tenv_def] >>
srw_tac[] [deBruijn_inc0, t_walkstar_FEMPTY] >>
full_simp_tac(srw_ss()) [t_walkstar_FEMPTY] >>
res_tac >>
metis_tac []);
*)


val tenv_inv_convert_env2 = Q.store_thm ("tenv_inv_convert_env2",
`∀env. check_env {} env ⇒ 
 tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)`,
  Induct >>
  srw_tac[] [convert_env2_def, bind_var_list2_def, tenv_inv_def] >>
  PairCases_on `h` >>
  Cases_on`h0=x`>>full_simp_tac(srw_ss())[lookup_tenv_def,bind_var_list2_def,bind_tenv_def,check_env_def]>>
  full_simp_tac(srw_ss())[deBruijn_inc0]
  >-
    (full_simp_tac(srw_ss())[check_t_to_check_freevars]>>
    qexists_tac`MAP (Tvar_db) (COUNT_LIST tvs)` >>
    full_simp_tac(srw_ss())[LENGTH_COUNT_LIST]>>
    CONJ_TAC
    >-
      full_simp_tac(srw_ss())[EVERY_MAP,COUNT_LIST_GENLIST,EVERY_GENLIST,check_freevars_def]
    >>
    match_mp_tac (deBruijn_subst_id |> CONJUNCT1)>>
    full_simp_tac(srw_ss())[check_t_to_check_freevars])
  >>
  full_simp_tac(srw_ss())[tenv_inv_def]>>
  res_tac>>
  Cases_on`check_t tvs {} t` >> full_simp_tac(srw_ss())[convert_env2_def])


val unconvert_t_def = tDefine "unconvert_t" `
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc)`
(wf_rel_tac `measure t_size` >>
 srw_tac[] [] >>
 induct_on `ts` >>
 srw_tac[] [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val unconvert_t_ind = theorem"unconvert_t_ind"

val check_freevars_empty_convert_unconvert_id = store_thm("check_freevars_empty_convert_unconvert_id",
``!t. check_freevars n [] t ⇒ convert_t (unconvert_t t) = t``,
  ho_match_mp_tac unconvert_t_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[unconvert_t_def,convert_t_def,check_freevars_def]>>
  full_simp_tac(srw_ss())[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM])

val check_t_empty_unconvert_convert_id = store_thm("check_t_empty_unconvert_convert_id",
``!t. check_t n {} t ⇒
  unconvert_t (convert_t t) = t``,
  ho_match_mp_tac (fetch "-" "convert_t_ind") >>
  srw_tac[][]>>
  full_simp_tac(srw_ss())[unconvert_t_def,convert_t_def,check_t_def]>>
  full_simp_tac(srw_ss())[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM])

val check_freevars_to_check_t = store_thm("check_freevars_to_check_t",
``!t z. check_freevars n [] t ⇒ check_t n {} (unconvert_t t)``,
  ho_match_mp_tac unconvert_t_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[unconvert_t_def,check_freevars_def,check_t_def]>>
  full_simp_tac(srw_ss())[EVERY_MAP,EVERY_MEM])

val tenv_invC_def = Define `
  tenv_invC s tenv tenvE =
  (∀x tvs t.
    lookup_tenv x 0 tenvE = SOME (tvs, t)
    ⇒
    (∃n. check_freevars n [] t) ∧ 
    (*Need a condition like this, not sure exactly what yet*)
    ∃tvs' t'.
    ALOOKUP tenv x = SOME(tvs',t') ∧
    (*Case split on whether we are inside an expression or not
      i.e. whether we have inferencer stuff in the types*)
    if check_t tvs' {} t'
    then
      (*Has no uvars*)
      ∃subst.
        LENGTH subst = tvs' ∧
        EVERY (check_t tvs {}) subst ∧ 
        infer_deBruijn_subst subst t' = unconvert_t t 
    else 
      tvs' = 0 ∧ tvs = 0 ∧ 
      unconvert_t t = t_walkstar s t')`

val tenv_alpha_def = Define`
  tenv_alpha tenv tenvE = 
    (tenv_inv FEMPTY tenv tenvE ∧
    tenv_invC FEMPTY tenv tenvE)` 

val infer_deBruijn_subst_id2 = store_thm("infer_deBruijn_subst_id2",
  ``(∀t.
  check_t tvs {} t ⇒  
  infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs) t = t) ∧ 
  (∀ts.
  EVERY (check_t tvs {}) ts ⇒  
  MAP (infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs)) ts = ts)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  srw_tac[][]>>full_simp_tac(srw_ss())[check_t_def]
  >-
    full_simp_tac(srw_ss())[infer_deBruijn_subst_def]
  >>
    full_simp_tac(srw_ss())[infer_deBruijn_subst_def,EVERY_MEM]>>
    metis_tac[])

val tenv_invC_convert_env2 = Q.store_thm ("tenv_invC_convert_env2",
`!env. check_env {} env ⇒ tenv_invC FEMPTY env (bind_var_list2 (convert_env2 env) Empty)`,
  Induct >>
  srw_tac[] [convert_env2_def, bind_var_list2_def, tenv_invC_def] >>
  full_simp_tac(srw_ss())[lookup_tenv_def]>>
  PairCases_on `h` >>
  Cases_on`h0=x`>>full_simp_tac(srw_ss())[lookup_tenv_def,bind_var_list2_def,bind_tenv_def,check_env_def]>>
  full_simp_tac(srw_ss())[deBruijn_inc0]
  >-
    metis_tac[check_t_to_check_freevars]
  >-
    (full_simp_tac(srw_ss())[tenv_invC_def,convert_env2_def]>>
    metis_tac[])
  >-
    (full_simp_tac(srw_ss())[check_t_to_check_freevars]>>
    qexists_tac`GENLIST Infer_Tvar_db tvs` >>
    full_simp_tac(srw_ss())[LENGTH_COUNT_LIST]>>
    CONJ_TAC
    >-
      full_simp_tac(srw_ss())[EVERY_MAP,COUNT_LIST_GENLIST,EVERY_GENLIST,check_t_def]
    >>
    qpat_assum `A=t` (SUBST_ALL_TAC o SYM)>>
    imp_res_tac check_t_empty_unconvert_convert_id>>
    full_simp_tac(srw_ss())[]>>
    match_mp_tac (infer_deBruijn_subst_id2 |> CONJUNCT1)>>
    full_simp_tac(srw_ss())[check_t_to_check_freevars])
  >>
  full_simp_tac(srw_ss())[tenv_invC_def,convert_env2_def])

val infer_deBruijn_subst_id = store_thm("infer_deBruijn_subst_id",
``(!t. infer_deBruijn_subst [] t = t) ∧ 
  (!ts. MAP (infer_deBruijn_subst []) ts = ts)``,
  Induct>>srw_tac[][]>>full_simp_tac(srw_ss())[infer_deBruijn_subst_def,MAP_EQ_ID])

val deBruijn_subst_nothing = store_thm("deBruijn_subst_nothing",
  ``(∀t.
  deBruijn_subst 0 [] t = t )∧
  ∀ts.
  MAP (deBruijn_subst 0 []) ts = ts``,
  ho_match_mp_tac astTheory.t_induction>>
  full_simp_tac(srw_ss())[deBruijn_subst_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[LIST_EQ_REWRITE]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[MEM_EL,EL_MAP])

val menv_alpha_def = Define`
  menv_alpha = fmap_rel (λitenv tenv. tenv_alpha itenv (bind_var_list2 tenv Empty))`

val sym_sub_tac = SUBST_ALL_TAC o SYM;

val generalise_subst_exist = store_thm("generalise_subst_exist",``
  (t_wfs s ∧ 
  (∀uv. uv ∈ FDOM s ⇒ check_t tvs {} (t_walkstar s (Infer_Tuvar uv))))
  ⇒
  (∀t subst n smap a b t'. 
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧ 
  t_vars t ⊆ FDOM s ∧
  check_t 0 (FDOM s) t ∧ 
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  generalise 0 n smap t = (a,b,t') ⇒
  ∃subst'. 
    LENGTH subst' = a ∧ 
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧ 
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x))) ∧ 
  (∀ts subst n smap a b ts'. 
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧ 
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧ 
  EVERY (λt. t_vars t ⊆ FDOM s) ts ∧ 
  EVERY (check_t 0 (FDOM s)) ts ∧ 
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  generalise_list 0 n smap ts = (a,b,ts') ⇒
  ∃subst'. 
    LENGTH subst' = a ∧ 
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧ 
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x)))``,
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  srw_tac[][]>>
  full_simp_tac(srw_ss())[check_t_def]
  >-
    (full_simp_tac(srw_ss())[generalise_def]>>
    qpat_assum`A=(a,b,t')` mp_tac>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]>>
    first_assum match_mp_tac>>
    ntac 2 HINT_EXISTS_TAC >>
    full_simp_tac(srw_ss())[EVERY_MEM,t_vars_eqn,SUBSET_DEF,MEM_MAP]>>
    metis_tac[])
  >-
    (imp_res_tac generalise_subst>>
    full_simp_tac(srw_ss())[generalise_def]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`[t_walkstar s (Infer_Tuvar n)]`>>
      qpat_assum`A=b` sym_sub_tac>>
      srw_tac[][]
      >-
        (simp[FAPPLY_FUPDATE_THM]>>
        `x ≠ n` by 
          (CCONTR_TAC>>
          full_simp_tac(srw_ss())[flookup_thm])>>
        full_simp_tac(srw_ss())[]>>
        `smap ' x < LENGTH subst` by full_simp_tac(srw_ss())[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>
        simp[EL_APPEND1])
      >>
      full_simp_tac(srw_ss())[t_vars_eqn,EL_LENGTH_APPEND])
    >>
    qexists_tac`[]`>>full_simp_tac(srw_ss())[EXTENSION]>>
    metis_tac[])
  >-
    (full_simp_tac(srw_ss())[generalise_def]>>
    qexists_tac`[]`>>full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[generalise_def]>>
    qpat_assum`A=(a,b,t')` mp_tac>>LET_ELIM_TAC>>
    imp_res_tac generalise_subst>>
    first_x_assum(qspecl_then[`subst`,`smap`,`num_gen`,`s'`,`t'`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then[`subst++subst'`,`s'`,`num_gen'`,`s''`,`ts''`] mp_tac)>>
    discharge_hyps>-
      (fsrw_tac [ARITH_ss] []>>
      reverse CONJ_TAC>-
        metis_tac[]>>
      full_simp_tac(srw_ss())[IN_FRANGE,SUBSET_DEF,PULL_EXISTS]>>
      gen_tac>>Cases_on`k ∈ FDOM smap`>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[SUBMAP_DEF]>>
      res_tac>>
      DECIDE_TAC)>>
    srw_tac[][]>>
    qexists_tac`subst'++subst''`>>full_simp_tac(srw_ss())[]>>
    metis_tac[])

val infer_deBruijn_subst_infer_subst_walkstar = store_thm("infer_deBruijn_subst_infer_subst_walkstar",``
  ∀b subst n m.
  FRANGE b ⊆ count (LENGTH subst) ∧
  t_wfs s 
  ⇒
  ((∀t.
  (∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  check_t 0 m t ∧
  t_vars t ⊆ FDOM b
  ⇒ 
  infer_deBruijn_subst subst (infer_subst b t) = 
  t_walkstar s t) ∧ 
  (∀ts.
  EVERY (λt.(∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x))) ts ∧ 
  EVERY (check_t 0 m) ts ∧ 
  EVERY (λt.t_vars t ⊆ FDOM b) ts 
  ⇒ 
  MAP ((infer_deBruijn_subst subst) o (infer_subst b)) ts = 
  MAP (t_walkstar s) ts))``,
  ntac 5 strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>srw_tac[][]>>
  full_simp_tac(srw_ss())[infer_subst_def,t_walkstar_eqn1,check_t_def,infer_deBruijn_subst_def]
  >-
    (full_simp_tac(srw_ss())[LIST_EQ_REWRITE,EL_MAP,t_vars_eqn,PULL_EXISTS,SUBSET_DEF,MEM_MAP]>>
    srw_tac[][]>>
    first_assum (match_mp_tac o MP_CANON)>>
    full_simp_tac(srw_ss())[EVERY_MEM]>>
    metis_tac[])
  >>
  (full_simp_tac(srw_ss())[t_vars_eqn] >> imp_res_tac flookup_thm>>
  full_simp_tac(srw_ss())[PULL_FORALL]>>
  full_simp_tac(srw_ss())[infer_deBruijn_subst_def]>>
  reverse IF_CASES_TAC
  >- (full_simp_tac(srw_ss())[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>metis_tac[])
  >> REFL_TAC))

val tenv_alpha_empty = store_thm("tenv_alpha_empty",``
  tenv_alpha [] (bind_var_list2 [] Empty)``,
  full_simp_tac(srw_ss())[tenv_alpha_def,bind_var_list2_def,tenv_inv_def,tenv_invC_def,lookup_tenv_def])

val tenv_alpha_convert = store_thm("tenv_alpha_convert",
  ``check_env ∅ tenv ⇒
    tenv_alpha tenv (bind_var_list2 (convert_env2 tenv) Empty) ``,
  srw_tac[][tenv_alpha_def,tenv_inv_convert_env2,tenv_invC_convert_env2])

val menv_alpha_convert = store_thm("menv_alpha_convert",
  ``check_menv menv ⇒ menv_alpha menv (convert_menv menv)``,
  srw_tac[][menv_alpha_def,convert_menv_def,fmap_rel_OPTREL_FLOOKUP,optionTheory.OPTREL_def,FLOOKUP_o_f] >>
  CASE_TAC >>
  full_simp_tac(srw_ss())[check_menv_def,FEVERY_ALL_FLOOKUP] >>
  res_tac >> full_simp_tac(srw_ss())[GSYM check_env_def] >>
  srw_tac[][GSYM convert_env2_def, tenv_alpha_convert])

val tenv_inv_bind_var_list2 = prove(``
  tenv_inv FEMPTY itenv (bind_var_list2 tenv Empty) ∧
  tenv_inv FEMPTY itenv' (bind_var_list2 tenv' Empty) ∧ 
  set (MAP FST itenv) = set (MAP FST tenv)  
  ⇒ 
  tenv_inv FEMPTY (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  srw_tac[][tenv_inv_def]>>
  full_simp_tac(srw_ss())[GSYM bvl2_lookup]>>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND]>>
  Cases_on`ALOOKUP itenv x`>>full_simp_tac(srw_ss())[]
  >-
    (`ALOOKUP tenv x = NONE` by metis_tac[ALOOKUP_NONE,EXTENSION]>>
    full_simp_tac(srw_ss())[])
  >>
    qpat_assum`x'=A` SUBST_ALL_TAC>>
    res_tac>>
    full_simp_tac(srw_ss())[])

val tenv_invC_bind_var_list2 = prove(``
  tenv_invC FEMPTY itenv (bind_var_list2 tenv Empty) ∧
  tenv_invC FEMPTY itenv' (bind_var_list2 tenv' Empty) ∧ 
  set (MAP FST itenv) = set (MAP FST tenv)  
  ⇒ 
  tenv_invC FEMPTY (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  srw_tac[][tenv_invC_def]>>
  full_simp_tac(srw_ss())[GSYM bvl2_lookup]>>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND]>>
  Cases_on `ALOOKUP tenv x`>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >-
    metis_tac[]
  >-
    (`ALOOKUP itenv x = NONE` by metis_tac[ALOOKUP_NONE,EXTENSION]>>
    full_simp_tac(srw_ss())[])
  >>
    qpat_assum`x'=A` SUBST_ALL_TAC>>
    res_tac>>
    full_simp_tac(srw_ss())[])

val tenv_alpha_bind_var_list2 = store_thm("tenv_alpha_bind_var_list2",``
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧
  set (MAP FST itenv) = set (MAP FST tenv) ∧  
  tenv_alpha itenv' (bind_var_list2 tenv' Empty)
  ⇒ 
  tenv_alpha (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  full_simp_tac(srw_ss())[tenv_alpha_def]>>
  metis_tac[tenv_inv_bind_var_list2,tenv_invC_bind_var_list2])

val check_weakE_EVERY = store_thm("check_weakE_EVERY",
  ``∀env_impl env_spec st.
      (∃st'. check_weakE env_impl env_spec st = (Success (),st')) ⇔
      EVERY (λ(n,tvs_spec,t_spec).
           case ALOOKUP env_impl n of
           | NONE => F
           | SOME (tvs_impl,t_impl) =>
               let t = infer_deBruijn_subst (GENLIST Infer_Tuvar tvs_impl) t_impl in
               IS_SOME (t_unify FEMPTY t_spec t)) env_spec``,
  ho_match_mp_tac check_weakE_ind >>
  conj_tac >- srw_tac[][check_weakE_def,success_eqns] >>
  srw_tac[][check_weakE_def] >>
  Cases_on`ALOOKUP env_impl n`>>simp[failwith_def] >>
  Cases_on`x`>>simp[success_eqns,init_state_def] >> full_simp_tac(srw_ss())[] >>
  simp[markerTheory.Abbrev_def] >>
  simp[init_infer_state_def] >>
  simp[COUNT_LIST_GENLIST,MAP_GENLIST,ETA_AX] >>
  simp[IS_SOME_EXISTS,PULL_EXISTS] >>
  srw_tac[][EQ_IMP_THM] >> srw_tac[][] >- (
    full_simp_tac(srw_ss())[LET_THM,IS_SOME_EXISTS] >>
    metis_tac[] ) >>
  simp[markerTheory.Abbrev_def,IS_SOME_EXISTS] )

val convert_env2_anub = store_thm("convert_env2_anub",
  ``∀ls ac. convert_env2 (anub ls ac) = anub (convert_env2 ls) ac``,
  Induct >> full_simp_tac(srw_ss())[anub_def,convert_env2_def] >>
  full_simp_tac(srw_ss())[UNCURRY] >>
  Cases >> full_simp_tac(srw_ss())[anub_def,UNCURRY] >> srw_tac[][] >>
  Cases_on`r`>>full_simp_tac(srw_ss())[])

val check_freevars_more = Q.prove (
`(!t x fvs1 fvs2.
  check_freevars x fvs1 t ⇒
  check_freevars x (fvs2++fvs1) t ∧
  check_freevars x (fvs1++fvs2) t) ∧
 (!ts x fvs1 fvs2.
  EVERY (check_freevars x fvs1) ts ⇒
  EVERY (check_freevars x (fvs2++fvs1)) ts ∧
  EVERY (check_freevars x (fvs1++fvs2)) ts)`,
Induct >>
srw_tac[] [check_freevars_def] >>
metis_tac []);

val t_to_freevars_check = Q.store_thm ("t_to_freevars_check",
`(!t st fvs st'.
   (t_to_freevars t (st:'a) = (Success fvs, st'))
   ⇒
   check_freevars 0 fvs t) ∧
 (!ts st fvs st'.
   (ts_to_freevars ts (st:'a) = (Success fvs, st'))
   ⇒
   EVERY (check_freevars 0 fvs) ts)`,
Induct >>
srw_tac[] [t_to_freevars_def, success_eqns, check_freevars_def] >>
srw_tac[] [] >>
metis_tac [check_freevars_more]);

val _ = export_theory ();
