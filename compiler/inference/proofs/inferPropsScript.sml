open preamble;
open libTheory namespacePropsTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory typeSysPropsTheory;

(*
local open semanticPrimitivesPropsTheory typeSoundInvariantsTheory in
val check_dup_ctors_cons = check_dup_ctors_cons;
val tenv_tabbrev_ok_def = tenv_tabbrev_ok_def;
val flat_tenv_tabbrev_ok_def = flat_tenv_tabbrev_ok_def;
end;
*)

val every_zip_split = Q.prove (
  `!l1 l2 P Q.
    LENGTH l1 = LENGTH l2 ⇒
    (EVERY (\(x,y). P x ∧ Q y) (ZIP (l1, l2)) ⇔ EVERY P l1 ∧ EVERY Q l2)`,
 Induct_on `l1`
 >> simp []
 >> Cases_on `l2`
 >> rw []
 >> metis_tac []);

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
rw [fmap_EXT]);

val _ = new_theory "inferProps";

val fevery_to_drestrict = Q.prove (
`!P m s.
  FEVERY P m ⇒ FEVERY P (DRESTRICT m s)`,
 rw [FEVERY_ALL_FLOOKUP,FLOOKUP_DRESTRICT]);

(* Not sure these are general enough to go elsewhere.*)
val flookup_update_list_none = Q.store_thm ("flookup_update_list_none",
`!x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (ALOOKUP l x = NONE))`,
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []);

val flookup_update_list_some = Q.store_thm ("flookup_update_list_some",
`!x m l y.
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((ALOOKUP (REVERSE l) x = SOME y) ∨
   ((ALOOKUP l x = NONE) ∧ (FLOOKUP m x = SOME y)))`,
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []);

val every_shim2 = Q.prove (
`!l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)`,
induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw [] >>
metis_tac []);

val every_shim = Q.store_thm ("every_shim",
`!l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)`,
induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw []);

val ienv_unchanged = Q.store_thm ("ienv_unchanged[simp]",
  `(ienv with inf_v := ienv.inf_v) = ienv ∧
   (ienv with inf_c := ienv.inf_c) = ienv ∧
   (ienv with inf_t := ienv.inf_t) = ienv`,
 rw [inf_env_component_equality]);

(* ---------- Facts about deBruijn increment ---------- *)

val infer_deBruijn_inc0 = Q.store_thm ("infer_deBruijn_inc0",
`!(n:num) t. infer_deBruijn_inc 0 t = t`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val infer_deBruijn_inc0_id = Q.store_thm ("infer_deBruijn_inc0_id",
`infer_deBruijn_inc 0 = (\x.x)`,
metis_tac [infer_deBruijn_inc0]);

val t_vars_inc = Q.store_thm ("t_vars_inc",
`!tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [t_vars_def, encode_infer_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw [encode_infer_t_def]);

val inc_wfs = Q.store_thm ("inc_wfs",
`!tvs s. t_wfs s ⇒ t_wfs (infer_deBruijn_inc tvs o_f s)`,
rw [t_wfs_eqn] >>
`t_vR s = t_vR (infer_deBruijn_inc tvs o_f s)`
       by (rw [FLOOKUP_o_f, FUN_EQ_THM, t_vR_eqn] >>
           full_case_tac  >>
           rw [t_vars_inc]) >>
metis_tac []);

val vwalk_inc = Q.store_thm ("vwalk_inc",
`!s tvs n.
  t_wfs s
  ⇒
  t_vwalk (infer_deBruijn_inc tvs o_f s) n = infer_deBruijn_inc tvs (t_vwalk s n)`,
rw [] >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
rw [] >>
Q.SPEC_TAC (`n`, `n`) >>
qpat_x_assum `!p. (!v. q v ⇒ p v) ⇒ !v. p v` ho_match_mp_tac >>
rw [] >>
imp_res_tac t_vwalk_eqn >>
once_asm_rewrite_tac [] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
cases_on `FLOOKUP s n` >>
rw [FLOOKUP_o_f, infer_deBruijn_inc_def] >>
cases_on `x` >>
rw [infer_deBruijn_inc_def]);

val walk_inc = Q.store_thm ("walk_inc",
`!s tvs t.
  t_wfs s
  ⇒
  t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) = infer_deBruijn_inc tvs (t_walk s t)`,
rw [] >>
cases_on `t` >>
rw [t_walk_eqn, infer_deBruijn_inc_def, vwalk_inc]);

val walkstar_inc = Q.store_thm ("walkstar_inc",
`!tvs s t.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) =
   infer_deBruijn_inc tvs (t_walkstar s t))`,
rw [] >>
imp_res_tac t_walkstar_ind >>
Q.SPEC_TAC (`t`, `t`) >>
pop_assum ho_match_mp_tac >>
rw [] >>
rw [walk_inc] >>
cases_on `t_walk s t` >>
rw [infer_deBruijn_inc_def] >>
imp_res_tac inc_wfs >>
rw [t_walkstar_eqn,infer_deBruijn_inc_def, walk_inc] >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum (fn _ => all_tac) >>
induct_on `l` >>
rw [] >>
fs []);

val walkstar_inc2 = Q.store_thm ("walkstar_inc2",
`!tvs s n.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
   infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))`,
rw [GSYM walkstar_inc, infer_deBruijn_inc_def]);

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
 rw [type_subst_def, infer_type_subst_def, t_walkstar_eqn1]
 >- (every_case_tac >>
     rw [t_walkstar_eqn1] >>
     fs [ALOOKUP_FAILS] >>
     fs [MAP_ZIP, LENGTH_COUNT_LIST, ALOOKUP_ZIP_MAP_SND] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
     metis_tac [])
 >- metis_tac []);

val infer_t_induction = infer_tTheory.infer_t_induction;

val infer_subst_FEMPTY = Q.store_thm ("infer_subst_FEMPTY",
`(!t. infer_subst FEMPTY t = t) ∧
 (!ts. MAP (infer_subst FEMPTY) ts = ts)`,
ho_match_mp_tac infer_t_induction >>
rw [SUBSET_DEF, infer_subst_def] >>
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
rw [SUBSET_DEF, infer_subst_def, t_vars_eqn] >|
[metis_tac [],
 full_case_tac >>
     full_case_tac >>
     rw [] >>
     fs [SUBMAP_DEF, FLOOKUP_DEF] >>
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
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     rw [] >>
     res_tac >>
     rw [EXTENSION, infer_subst_def] >>
     fs [t_vars_eqn] >>
     metis_tac [],
 rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     rw [FLOOKUP_DEF, EXTENSION] >>
     TRY (EQ_TAC) >>
     rw [] >>
     fs [FLOOKUP_DEF, infer_subst_def, t_vars_eqn] >>
     decide_tac,
 REPEAT GEN_TAC >>
     STRIP_TAC >>
     `?tvs s' t'. generalise m n s t = (tvs, s', t')`
               by (cases_on `generalise m n s t` >>
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     `?tvs s' ts'. generalise_list m (tvs'+n) s'' ts = (tvs, s', ts')`
               by (cases_on `generalise_list m (tvs'+n) s'' ts` >>
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     qpat_x_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `tvs'+n`, `s''`, `tvs''`, `s'''`, `ts''`]) >>
     qpat_x_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `n`, `s`, `tvs'`, `s''`, `t'`]) >>
     rw [INTER_UNION] >|
     [metis_tac [SUBMAP_TRANS],
      rw [EXTENSION] >>
          metis_tac [],
      `uv ∈ FDOM s''` by fs [] >>
          res_tac >>
          rw [INTER_UNION] >>
          fs [SUBMAP_DEF],
      `uv ∈ FDOM s''` by fs [] >>
          res_tac >>
          rw [INTER_UNION] >>
          fs [SUBMAP_DEF] >>
          res_tac >>
          decide_tac,
      `uv ∈ FDOM s'` by (fs [] >> metis_tac []) >>
          cases_on `uv ∈ t_vars t` >>
          rw [] >>
          res_tac >>
          rw [INTER_UNION] >>
          fs [SUBMAP_DEF] >>
          res_tac >>
          decide_tac,
      `uv ∈ FDOM s'` by (fs [] >> metis_tac []) >>
          cases_on `uv ∈ t_vars t` >>
          rw [] >|
          [`uv ∈ FDOM s''` by (fs [] >> metis_tac []) >>
               res_tac >>
               rw [INTER_UNION] >>
               fs [SUBMAP_DEF] >>
               res_tac >>
               decide_tac],
      metis_tac [],
      metis_tac [],
      `{uv | uv ∈ t_vars t ∧ m ≤ uv} ⊆ FDOM s'' ∧ (!uv. uv ∈ FDOM s' DIFF FDOM s'' ⇒ m ≤ uv)`
               by rw [SUBSET_DEF] >>
          metis_tac [infer_subst_submap],
      `{uv | ∃s. uv ∈ s ∧ MEM s (MAP t_vars ts'') ∧ m ≤ uv} ⊆ FDOM s ∧ (!uv. uv ∈ FDOM s'' DIFF FDOM s ⇒ m ≤ uv)`
                     by (rw [SUBSET_DEF] >>
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
rw [] >>
imp_res_tac generalise_subst >>
fs [] >>
rw [] >|
[rw [BIGUNION, EXTENSION] >>
     metis_tac [],
 fs [EXTENSION] >>
     metis_tac [],
 cases_on `ts'` >>
     rw [] >>
     rw [EXTENSION] >>
     eq_tac >>
     rw [] >>
     fs [t_vars_eqn] >>
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
rw [] >>
cases_on `st` >>
rw [infer_st_component_equality]);

val st_ex_return_success = Q.prove (
`!v st v' st'.
  (st_ex_return v st = (Success v', st')) =
  ((v = v') ∧ (st = st'))`,
rw [st_ex_return_def]);

val st_ex_bind_success = Q.prove (
`!f g st st' v.
 (st_ex_bind f g st = (Success v, st')) =
 ?v' st''. (f st = (Success v', st'')) /\ (g v' st'' = (Success v, st'))`,
rw [st_ex_bind_def] >>
cases_on `f st` >>
rw [] >>
cases_on `q` >>
rw []);

val fresh_uvar_success = Q.prove (
`!st t st'.
  (fresh_uvar st = (Success t, st')) =
  ((t = Infer_Tuvar st.next_uvar) ∧
   (st' = st with next_uvar := st.next_uvar + 1))`,
rw [fresh_uvar_def] >>
metis_tac []);

val n_fresh_uvar_success = Q.prove (
`!n st ts st'.
  (n_fresh_uvar n st = (Success ts, st')) =
  ((ts = MAP (\n. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST n)) ∧
   (st' = st with next_uvar := st.next_uvar + n))`,
ho_match_mp_tac n_fresh_uvar_ind >>
rw [] >>
rw [st_ex_return_success, Once n_fresh_uvar_def, COUNT_LIST_SNOC,
    st_ex_bind_success, fresh_uvar_success, infer_st_rewrs] >-
metis_tac [] >>
fs [] >>
srw_tac [ARITH_ss] [] >>
rw [count_list_sub1, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
eq_tac >>
srw_tac [ARITH_ss] [arithmeticTheory.ADD1]);

val apply_subst_success = Q.prove (
`!t1 st1 t2 st2.
  (apply_subst t1 st1 = (Success t2, st2))
  =
  ((st2 = st1) ∧
   (t2 = t_walkstar st1.subst t1))`,
rw [st_ex_return_def, st_ex_bind_def, LET_THM, apply_subst_def, read_def] >>
eq_tac >>
rw []);

val add_constraint_success = Q.store_thm ("add_constraint_success",
`!t1 t2 st st' x.
  (add_constraint t1 t2 st = (Success x, st'))
  =
  ((x = ()) ∧ (?s. (t_unify st.subst t1 t2 = SOME s) ∧ (st' = st with subst := s)))`,
rw [add_constraint_def] >>
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
rw [add_constraints_def, pure_add_constraints_def, st_ex_return_success,
    failwith_def, st_ex_bind_success, add_constraint_success] >>
TRY (cases_on `x`) >>
rw [pure_add_constraints_def] >-
metis_tac [infer_st_component_equality] >>
eq_tac >>
rw [] >>
fs [infer_st_subst] >>
cases_on `t_unify st.subst t1 t2` >>
fs []);

val failwith_success = Q.prove (
`!m st v st'. (failwith m st = (Success v, st')) = F`,
rw [failwith_def]);

val lookup_st_ex_success = Q.prove (
`!x l st v st'.
  (lookup_st_ex x l st = (Success v, st'))
  =
  ((nsLookup l x = SOME v) ∧ (st = st'))`,
 rw [lookup_st_ex_def, failwith_def, st_ex_return_success]
 >> every_case_tac);

val op_case_expand = Q.prove (
`!f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 op st v st'.
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
     | Aupdate => f24
     | FFI n => f25
     | WordFromInt wz => f26
     | WordToInt wz => f27
     | Opw wz opw => f28
     | Shift wz sh n => f29) st
   = (Success v, st'))
  =
  ((?opn. (op = Opn opn) ∧ (f1 st = (Success v, st'))) ∨
   (?opb. (op = Opb opb) ∧ (f2 st = (Success v, st'))) ∨
   (?wz opw. (op = Opw wz opw) ∧ (f28 st = (Success v, st'))) ∨
   (?wz sh n. (op = Shift wz sh n) ∧ (f29 st = (Success v, st'))) ∨
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
   ((?wz. op = WordFromInt wz) ∧ (f26 st = (Success v, st'))) ∨
   ((?wz. op = WordToInt wz) ∧ (f27 st = (Success v, st'))) ∨
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
   ((op = Aupdate) ∧ (f24 st = (Success v, st'))) ∨
   (?n. (op = FFI n) ∧ (f25 st = (Success v, st'))))`,
rw [] >>
cases_on `op` >>
rw []);

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
rw [get_next_uvar_def] >>
metis_tac []);

val apply_subst_list_success =
  SIMP_CONV (srw_ss()) [apply_subst_list_def, LET_THM]
  ``(apply_subst_list ts st = (Success v, st'))``

val guard_success = Q.prove (
`∀P m st v st'.
  (guard P m st = (Success v, st'))
  =
  (P ∧ (v = ()) ∧ (st = st'))`,
rw [guard_def, st_ex_return_def, failwith_def] >>
metis_tac []);

val option_case_eq = Q.prove (
`!opt f g v st st'.
  ((case opt of NONE => f | SOME x => g x) st = (Success v, st')) =
  (((opt = NONE) ∧ (f st = (Success v, st'))) ∨ (?x. (opt = SOME x) ∧ (g x st = (Success v, st'))))`,
rw [] >>
cases_on `opt` >>
fs []);

val success_eqns =
  LIST_CONJ [st_ex_return_success, st_ex_bind_success, fresh_uvar_success,
             apply_subst_success, add_constraint_success, lookup_st_ex_success,
             n_fresh_uvar_success, failwith_success, add_constraints_success,
             oneTheory.one,
             get_next_uvar_success, apply_subst_list_success, guard_success,
             read_def, option_case_eq];

val _ = save_thm ("success_eqns", success_eqns);

(* ---------- Simple structural properties ---------- *)

val remove_pair_lem = Q.store_thm ("remove_pair_lem",
`(!f v. (\(x,y). f x y) v = f (FST v) (SND v)) ∧
 (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND (SND v)))`,
rw [] >>
PairCases_on `v` >>
rw []);

val infer_funs_length = Q.store_thm ("infer_funs_length",
`!ienv funs ts st1 st2.
  (infer_funs ienv funs st1 = (Success ts, st2)) ⇒
  (LENGTH funs = LENGTH ts)`,
induct_on `funs` >>
rw [infer_e_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
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
rw [pat_bindings_def, infer_p_def, success_eqns, remove_pair_lem] >>
rw []
>- (PairCases_on `v'` >>
    rw [] >>
    metis_tac [])
>- (PairCases_on `v''` >>
    rw [] >>
    metis_tac [])
>- (PairCases_on `v'` >>
    rw [] >>
    metis_tac [])
>- metis_tac []
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    rw [] >>
    metis_tac [APPEND_ASSOC]));

(* ---------- Dealing with the constraint set ---------- *)

val pure_add_constraints_append2 = Q.prove (
`!s1 ts s2 t1 t2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
induct_on `ts` >>
rw [pure_add_constraints_def] >>
rw [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs, t_unify_apply2]);

val pure_add_constraints_apply = Q.store_thm ("pure_add_constraints_apply",
`!s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts`,
induct_on `ts` >>
rw [pure_add_constraints_def] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_apply, pure_add_constraints_append2, t_unify_wfs]);

val pure_add_constraints_append = Q.store_thm ("pure_add_constraints_append",
`!s1 ts1 s3 ts2.
  pure_add_constraints s1 (ts1 ++ ts2) s3
  =
  (?s2. pure_add_constraints s1 ts1 s2 ∧ pure_add_constraints s2 ts2 s3)`,
ho_match_mp_tac pure_add_constraints_ind >>
rw [pure_add_constraints_def] >>
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
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def]);

val infer_e_constraints = Q.store_thm ("infer_e_constraints",
`(!ienv e st st' t.
    (infer_e ienv e st = (Success t, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!ienv es st st' ts.
    (infer_es ienv es st = (Success ts, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!ienv pes t1 t2 st st'.
    (infer_pes ienv pes t1 t2 st = (Success (), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!ienv funs st st' ts'.
    (infer_funs ienv funs st = (Success ts', st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst))`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
TRY (cases_on `v'`) >>
every_case_tac >>
fs [success_eqns] >>
rw [] >>
fs [infer_st_rewrs] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, infer_p_constraints]);

val pure_add_constraints_wfs = Q.store_thm ("pure_add_constraints_wfs",
`!s1 ts s2.
  pure_add_constraints s1 ts s2 ∧
  t_wfs s1
  ⇒
  t_wfs s2`,
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
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
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``,
           arithmeticTheory.LESS_EQ_TRANS]);

val infer_e_next_uvar_mono = Q.store_thm ("infer_e_next_uvar_mono",
`(!ienv e st st' t.
    (infer_e ienv e st = (Success t, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!ienv es st st' ts.
    (infer_es ienv es st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!ienv pes t1 t2 st st'.
    (infer_pes ienv pes t1 t2 st = (Success (), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!ienv funs st st' ts.
    (infer_funs ienv funs st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
every_case_tac >>
fs [success_eqns] >>
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
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs []
>- prove_tac [pure_add_constraints_wfs]
>- metis_tac [t_unify_wfs])

val infer_e_wfs = Q.store_thm ("infer_e_wfs",
`(!ienv e st st' t.
    (infer_e ienv e st = (Success t, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!ienv es st st' ts.
    (infer_es ienv es st = (Success ts, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!ienv pes t1 t2 st st'.
    (infer_pes ienv pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!ienv funs st st' ts'.
    (infer_funs ienv funs st = (Success ts', st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst)`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
fs [] >>
res_tac >>
imp_res_tac t_unify_wfs >>
fs [] >>
imp_res_tac pure_add_constraints_wfs >>
fs [] >>
TRY (cases_on `v'`) >>
imp_res_tac infer_p_wfs >>
fs [] >>
every_case_tac >>
fs [success_eqns] >>
rw [] >>
fs [infer_st_rewrs] >>
res_tac >>
fs [] >>
imp_res_tac t_unify_wfs);

(* ---------- The invariants of the inferencer ---------- *)

val check_t_more = Q.store_thm ("check_t_more",
`(!t tvs. check_t tvs {} t ⇒ !uvs. check_t tvs uvs t) ∧
 (!ts tvs. EVERY (check_t tvs {}) ts ⇒ !uvs. EVERY (check_t tvs uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []);

val check_t_more2 = Q.store_thm ("check_t_more2",
`(!t tvs uvs. check_t tvs uvs t ⇒ !tvs'. check_t (tvs' + tvs) uvs t) ∧
 (!ts tvs uvs. EVERY (check_t tvs uvs) ts ⇒ !tvs'. EVERY (check_t (tvs' + tvs) uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []);

val check_t_more3 = Q.store_thm ("check_t_more3",
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. check_t tvs (count (uvs + uvs')) t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. EVERY (check_t tvs (count (uvs + uvs'))) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
metis_tac [] >>
decide_tac);

val check_t_more4 = Q.store_thm ("check_t_more4",
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. uvs ≤ uvs' ⇒ check_t tvs (count uvs') t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. uvs ≤ uvs' ⇒ EVERY (check_t tvs (count uvs')) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac [ARITH_ss] [check_t_def] >>
metis_tac []);

val check_t_more5 = Q.store_thm ("check_t_more5",
`(!t uvs tvs. check_t tvs uvs t ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_t tvs uvs' t) ∧
 (!ts uvs tvs. EVERY (check_t tvs uvs) ts ⇒ !uvs'. uvs ⊆ uvs' ⇒ EVERY (check_t tvs uvs') ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, SUBSET_DEF] >>
metis_tac []);

val check_t_t_vars = Q.store_thm ("check_t_t_vars",
`!tvs uvs t.
  check_t tvs uvs t ⇒ t_vars t ⊆ uvs`,
ho_match_mp_tac check_t_ind >>
rw [t_vars_eqn, check_t_def, EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
metis_tac []);

val check_s_more = Q.prove (
`!s tvs uvs. check_s tvs (count uvs) s ⇒ check_s tvs (count (uvs + 1)) s`,
rw [check_s_def] >>
metis_tac [check_t_more3]);

val check_s_more2 = Q.store_thm ("check_s_more2",
`!s uvs. check_s tvs (count uvs) s ⇒ !uvs'. uvs ≤ uvs' ⇒ check_s tvs (count uvs') s`,
rw [check_s_def] >>
metis_tac [check_t_more4]);

val check_s_more3 = Q.store_thm ("check_s_more3",
`!s uvs. check_s tvs uvs s ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_s tvs uvs' s`,
rw [check_s_def] >>
metis_tac [check_t_more5]);

val check_t_deBruijn_inc2 = Q.prove (
`!inc t. check_t tvs {} t ⇒ check_t (inc + tvs) {} (infer_deBruijn_inc inc t)`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [check_t_def, infer_deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM]);

val check_t_deBruijn_inc = Q.store_thm ("check_t_deBruijn_inc",
`!inc t. check_t 0 UNIV t ⇒ (infer_deBruijn_inc inc t = t)`,
ho_match_mp_tac infer_deBruijn_inc_ind >>
rw [check_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val check_t_subst = Q.store_thm ("check_t_subst",
`!tvs (tvs':num set) t s.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`,
ho_match_mp_tac check_t_ind >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw []);

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
rw [] >>
rw [Once t_vwalk_eqn] >>
cases_on `FLOOKUP s n` >>
rw [check_t_def] >>
cases_on `x` >>
rw [check_t_def] >>
fs [check_s_def, FLOOKUP_DEF] >>
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
rw [] >>
rw [t_walkstar_eqn] >>
cases_on `t` >>
fs [check_t_def] >>
rw [t_walk_eqn] >>
rw [check_t_def, EVERY_MAP] >|
[fs [EVERY_MEM] >>
     rw [] >>
     fs [t_walk_eqn],
 fs [t_walk_eqn] >>
     `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)`
             by metis_tac [t_vwalk_check,  IN_UNION] >>
     cases_on `t_vwalk s n` >>
     fs [check_t_def, EVERY_MAP] >>
     fs [EVERY_MEM] >>
     metis_tac [t_vwalk_to_var],
 fs [t_walk_eqn] >>
     `check_t tvs (uvs ∪ FDOM s) (t_vwalk s n)`
             by metis_tac [t_vwalk_check,  IN_UNION] >>
     cases_on `t_vwalk s n` >>
     fs [check_t_def, EVERY_MAP] >>
     fs [EVERY_MEM] >>
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
rw [] >|
[qpat_x_assum `t_unify s t1 t2 = SOME s'` mp_tac >>
     rw [t_unify_eqn] >>
     cases_on `t1` >>
     cases_on `t2` >>
     fs [t_walk_eqn, t_ext_s_check_eqn, check_t_def] >|
     [`check_t tvs uvs (t_vwalk s n')` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n'` >>
          fs [check_t_def] >>
          fs [check_s_def] >>
          rw [check_t_def] >>
          rw [check_t_def, FAPPLY_FUPDATE_THM],
      metis_tac [],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          fs [check_t_def] >-
          metis_tac [] >>
          fs [check_s_def] >>
          rw [check_t_def] >>
          rw [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          fs [check_t_def] >>
          fs [check_s_def] >>
          rw [check_t_def] >>
          rw [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          fs [check_t_def] >-
          metis_tac [] >>
          fs [check_s_def] >>
          rw [check_t_def] >>
          rw [check_t_def, FAPPLY_FUPDATE_THM],
      `check_t tvs uvs (t_vwalk s n)` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n` >>
          `check_t tvs uvs (t_vwalk s n')` by metis_tac [t_vwalk_check] >>
          cases_on `t_vwalk s n'` >>
          fs [check_t_def] >>
          TRY (fs [check_s_def] >>
               rw [check_t_def, FAPPLY_FUPDATE_THM] >>
               rw [check_t_def] >>
               NO_TAC) >>
          metis_tac []],
 pop_assum mp_tac >>
     cases_on `ts1` >>
     cases_on `ts2` >>
     fs [ts_unify_def] >>
     rw [] >-
     metis_tac [] >>
     cases_on `t_unify s h h'` >>
     fs []]);

val check_t_walkstar = Q.store_thm ("check_t_walkstar",
`(!t tvs s.
    t_wfs s ∧
    check_t tvs (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    check_t tvs {} (t_walkstar s t)) ∧
 (!ts tvs s.
    t_wfs s ∧
    EVERY (check_t tvs (FDOM s)) ts ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    EVERY (check_t tvs {} o t_walkstar s) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, t_walkstar_eqn1, EVERY_MAP] >>
metis_tac []);

val t_walkstar_no_vars = Q.store_thm ("t_walkstar_no_vars",
`!tvs (tvs':num set) t s.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t_walkstar s t = t)`,
ho_match_mp_tac check_t_ind >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw [] >>
metis_tac []);

val t_unify_check_s = Q.store_thm ("t_unify_check_s",
`!s1 tvs uvs t1 t2 s2.
  t_unify s1 t1 t2 = SOME s2 ∧
  t_wfs s1 ∧
  check_s tvs uvs s1 ∧
  check_t tvs uvs t1 ∧
  check_t tvs uvs t2
  ⇒
  check_s tvs uvs s2`,
metis_tac [t_unify_check_s_help]);

val pure_add_constraints_check_s = Q.store_thm ("pure_add_constraints_check_s",
`!s1 tvs uvs ts s2.
  pure_add_constraints s1 ts s2 ∧
  t_wfs s1 ∧
  EVERY (\(t1,t2). check_t tvs (count uvs) t1 ∧ check_t tvs (count uvs) t2) ts ∧
  check_s tvs (count uvs) s1
  ⇒
  check_s tvs (count uvs) s2`,
induct_on `ts` >-
(rw [check_s_def, pure_add_constraints_def] >-
 metis_tac []) >>
rw [pure_add_constraints_def] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
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
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [check_t_def]
>- (PairCases_on `v'` >>
    fs [remove_pair_lem, EVERY_MEM] >>
    rw [] >>
    metis_tac [check_t_more3])
>- (PairCases_on `v'` >>
    fs [] >>
    metis_tac [])
>- (PairCases_on `v''` >>
    fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
    rw [check_t_def] >>
    `?n. st'.next_uvar = st'''.next_uvar + n`
                by (imp_res_tac infer_p_next_uvar_mono >>
                    qexists_tac `st'.next_uvar - st'''.next_uvar` >>
                    srw_tac [ARITH_ss] []) >>
    metis_tac [check_t_more3])
>- (PairCases_on `v''` >>
    fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
    rw [check_t_def] >>
    decide_tac)
>- (PairCases_on `v'` >>
    fs [] >>
    metis_tac [])
>- (PairCases_on `v'` >>
    fs [] >>
    metis_tac [])
>- metis_tac []
>- metis_tac []
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    fs [] >>
    metis_tac [infer_p_wfs])
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    fs [remove_pair_lem, EVERY_MEM] >>
    rw [] >>
    `?n. st'.next_uvar = st''.next_uvar + n`
                by (imp_res_tac infer_p_next_uvar_mono >>
                    qexists_tac `st'.next_uvar - st''.next_uvar` >>
                    srw_tac [ARITH_ss] []) >>
    metis_tac [check_t_more3])
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    fs [] >>
    `?n. st'.next_uvar = st''.next_uvar + n`
                by (imp_res_tac infer_p_next_uvar_mono >>
                    qexists_tac `st'.next_uvar - st''.next_uvar` >>
                    srw_tac [ARITH_ss] []) >>
    metis_tac [check_t_more3])
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    fs [] >>
    `?n. st'.next_uvar = st''.next_uvar + n`
                by (imp_res_tac infer_p_next_uvar_mono >>
                    qexists_tac `st'.next_uvar - st''.next_uvar` >>
                    srw_tac [ARITH_ss] []) >>
    metis_tac [infer_p_wfs, check_t_more3]));

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
rw [check_freevars_def, check_t_def, infer_type_subst_def] >|
[pop_assum mp_tac >>
     Q.SPEC_TAC (`uvs`, `uvs`) >>
     induct_on `tvs` >>
     rw [COUNT_LIST_def, check_t_def] >>
     qpat_x_assum `!uvs. P uvs` (mp_tac o Q.SPEC `SUC uvs`) >>
     rw [MAP_MAP_o, combinTheory.o_DEF] >>
     qmatch_asmsub_abbrev_tac`MAP f1 _` >>
     qmatch_goalsub_abbrev_tac`MAP f2 _` >>
     `f1 = f2` by (unabbrev_all_tac \\ simp[FUN_EQ_THM]) >>
     fs[ADD1],
 metis_tac [EVERY_MAP]]);

(* moved this one arround a bit *)
val infer_type_subst_empty_check = store_thm("infer_type_subst_empty_check",``
(∀t.
  check_freevars 0 [] t ⇒
  check_t 0 {} (infer_type_subst [] t)) ∧
∀ts.
EVERY (check_freevars 0 []) ts ⇒
EVERY (check_t 0 {}) (MAP (infer_type_subst []) ts)``,
                                             Induct>>fs[check_freevars_def,infer_type_subst_def,check_t_def]>>
                                                   metis_tac[]);

val infer_p_check_s = Q.store_thm ("infer_p_check_s",
  `(!ienv p st t env st' tvs.
    infer_p ienv p st = (Success (t,env), st') ∧
    t_wfs st.subst ∧
    tenv_ctor_ok ienv.inf_c ∧
    tenv_abbrev_ok ienv.inf_t ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
   (!ienv ps st ts env st' tvs.
    infer_ps ienv ps st = (Success (ts,env), st') ∧
    t_wfs st.subst ∧
    tenv_ctor_ok ienv.inf_c ∧
    tenv_abbrev_ok ienv.inf_t ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst)`,
 ho_match_mp_tac infer_p_ind >>
 rw [infer_p_def, success_eqns, remove_pair_lem] >>
 rw []
 >- metis_tac [check_s_more]
 >- (PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono])
 >- (rename1 `infer_ps _ _ _ = (Success v1, st1)` >>
     PairCases_on `v1` >>
     fs [] >>
     first_x_assum drule >>
     rpt (disch_then drule) >>
     drule (CONJUNCT2 infer_p_wfs) >>
     rpt (disch_then drule) >>
     rw []>>
     `st1.next_uvar ≤ st1.next_uvar + LENGTH (FST v')` by decide_tac >>
     `check_s tvs (count st'.next_uvar) st1.subst` by metis_tac [check_s_more2,ADD_COMM] >>
     match_mp_tac pure_add_constraints_check_s >>
     qexists_tac `st1.subst` >>
     qexists_tac `(ZIP (v10, MAP (infer_type_subst (ZIP (FST v', MAP (λn.  Infer_Tuvar (st1.next_uvar + n)) (COUNT_LIST (LENGTH (FST v')))))) (FST (SND v'))))` >>
     rw [] >>
     rw [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
     metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_p_next_uvar_mono,
                arithmeticTheory.LESS_EQ_TRANS, infer_p_check_t, ADD_COMM] >>
     PairCases_on `v'` >>
     fs [] >>
     imp_res_tac tenv_ctor_ok_lookup >>
     imp_res_tac check_infer_type_subst >>
     rw [] >>
     fs [EVERY_MEM] >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM])
 >- (PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono])
 >- (irule t_unify_check_s >>
     qexists_tac `st''.subst` >>
     qexists_tac `t'` >>
     qexists_tac `(infer_type_subst [] (type_name_subst ienv.inf_t t))` >>
     rw []
     >- metis_tac [infer_p_wfs]
     >- metis_tac [t_unify_check_s]
     >- metis_tac [check_t_more2, arithmeticTheory.ADD_0, infer_p_check_t, ADD_COMM]
     >- metis_tac [infer_type_subst_empty_check, check_freevars_type_name_subst,
                   check_t_more2, arithmeticTheory.ADD_0, infer_p_check_t, ADD_COMM, check_t_more])
 >- (PairCases_on `v'` >>
     PairCases_on `v''` >>
     metis_tac [infer_p_wfs, check_s_more2, infer_p_next_uvar_mono]));

val check_env_more = Q.store_thm ("check_env_more",
`!uvs e.
  nsAll (λx (tvs,t). check_t tvs (count uvs) t) e
  ⇒
  !uvs'. uvs ≤ uvs' ⇒ nsAll (λx (tvs,t). check_t tvs (count uvs') t) e`,
 rw []
 >> irule nsAll_mono
 >> qexists_tac `(λx (tvs,t). check_t tvs (count uvs) t)`
 >> rw []
 >> pairarg_tac
 >> fs []
 >> metis_tac [check_t_more4]);

val check_env_letrec_lem = Q.store_thm ("check_env_letrec_lem",
`∀uvs funs uvs'.
  ((funs = []) ∨ (uvs' + LENGTH funs ≤ uvs))
  ⇒
  nsAll (λx (tvs,t). check_t tvs (count uvs) t)
    (alist_to_ns (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (n+uvs')) (COUNT_LIST (LENGTH funs)))))`,
 rw [COUNT_LIST_def]
 >> rw [COUNT_LIST_def]
 >> irule nsAll_alist_to_ns
 >> Induct_on `funs`
 >> rw [COUNT_LIST_def]
 >> rpt (pairarg_tac >> fs [])
 >> rw [check_t_def]
 >> fs [MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM]
 >> rw []
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [MAP2_MAP, LENGTH_COUNT_LIST, MEM_MAP, MEM_ZIP]
 >> rw []
 >> fs []
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [EL_MAP, LENGTH_COUNT_LIST, check_t_def, EL_COUNT_LIST]);

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
rw [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST,
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
rw [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST,
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >-
metis_tac []);

val infer_e_check_t = Q.store_thm ("infer_e_check_t",
  `(!ienv e st st' t.
    infer_e ienv e st = (Success t, st') ∧
    ienv_val_ok (count st.next_uvar) ienv.inf_v
    ⇒
    check_t 0 (count st'.next_uvar) t) ∧
   (!ienv es st st' ts.
    infer_es ienv es st = (Success ts, st') ∧
    ienv_val_ok (count st.next_uvar) ienv.inf_v
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts) ∧
   (!ienv pes t1 t2 st st'.
    infer_pes ienv pes t1 t2 st = (Success (), st') ∧
    ienv_val_ok (count st.next_uvar) ienv.inf_v
    ⇒
    T) ∧
   (!ienv funs st st' ts'.
    infer_funs ienv funs st = (Success ts', st') ∧
    ienv_val_ok (count st.next_uvar) ienv.inf_v
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts')`,
 ho_match_mp_tac infer_e_ind >>
 srw_tac[] [infer_e_def, constrain_op_success, success_eqns, remove_pair_lem] >>
 fsrw_tac[] [check_t_def] >>
 imp_res_tac infer_e_next_uvar_mono >>
 fsrw_tac[] [EVERY_MAP, check_t_def, check_t_infer_db_subst]
 >- metis_tac [check_t_more4]
 >- (fs [ienv_val_ok_def] >>
     imp_res_tac nsLookup_nsAll >>
     pairarg_tac >>
     fs [] >>
     pairarg_tac >>
     fs [] >>
     srw_tac[] [] >>
     metis_tac [check_t_more3, ADD_COMM])
 >- metis_tac [check_t_more4]
 >- (rw [EVERY_MEM, MEM_COUNT_LIST] >>
     decide_tac)
 >- (srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def, ienv_val_ok_def] >>
     first_x_assum irule >>
     irule nsAll_nsBind >>
     simp [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``])
 >- (every_case_tac >>
     fs [success_eqns] >>
     rw [] >>
     fs [infer_st_rewrs, EVERY_MAP, check_t_def, check_t_infer_db_subst] >>
     res_tac >>
     fs [])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> simp []
   >> fs [ienv_val_ok_def]
   >> metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4])
 >- decide_tac
 >- (res_tac >>
     fs [check_t_def] >>
     pop_assum match_mp_tac  >>
     rw [opt_bind_def] >>
     every_case_tac >>
     fs [ienv_val_ok_def] >>
     irule nsAll_nsOptBind
     >> simp [option_nchotomy]
     >> metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> simp []
   >> fs [ienv_val_ok_def]
   >> rw []
   >> first_x_assum irule
   >> irule nsAll_nsAppend
   >> simp []
   >- (
     irule check_env_letrec_lem
     >> simp [])
   >> irule check_env_more
   >> `st.next_uvar ≤ st''''.next_uvar` by decide_tac
   >> metis_tac [check_env_more, check_t_more4])
 >- (res_tac >>
     fs [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4])
 >- (res_tac >>
     fs [ienv_val_ok_def] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4])
 >- (reverse (srw_tac [ARITH_ss] []) >>
     res_tac >>
     fs [check_t_def, ienv_val_ok_def]
     >- metis_tac [check_env_more, check_t_more4, DECIDE ``x ≤ x + 1:num``]
     >> `check_t 0 (count st'''.next_uvar) t` suffices_by metis_tac [check_t_more4]
     >> first_x_assum irule
     >> irule nsAll_nsBind
     >> simp [check_t_def]
     >> metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]));

val constrain_op_check_s = Q.prove (
`!tvs op ts t st st'.
  constrain_op op ts st = (Success t, st') ∧
  t_wfs st.subst ∧
  EVERY (check_t 0 (count st.next_uvar)) ts ∧
  check_s tvs (count st.next_uvar) st.subst
  ⇒
  check_s tvs (count st'.next_uvar) st'.subst`,
 rw [constrain_op_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_int)` by rw [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_word8)` by rw [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_word8array)` by rw [check_t_def] >>
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_string)` by rw [check_t_def] >>
 `!uvs tvs wz. check_t tvs uvs (Infer_Tapp [] (TC_word wz))` by rw [check_t_def] >>
 every_case_tac >>
 fs [success_eqns] >>
 rw [] >>
 fs [infer_st_rewrs]
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
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar+1)) (Infer_Tapp [h'; Infer_Tuvar st.next_uvar] TC_fn)`
              by (rw [check_t_def] >>
                  metis_tac [check_t_more3]) >>
     `check_t 0 (count (st.next_uvar + 1)) h`
                    by metis_tac [EVERY_DEF, check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_s tvs (count (st.next_uvar+1)) st.subst`
            by metis_tac [check_s_more] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count st.next_uvar) (Infer_Tapp [h'] TC_ref)`
              by rw [check_t_def] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar+1)) (Infer_Tapp [Infer_Tuvar st.next_uvar] TC_ref)`
              by (rw [check_t_def] >>
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
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     `check_s tvs (count st.next_uvar) s'`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     `check_s tvs (count st.next_uvar) s'`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_char)` by rw [check_t_def] >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``t_unify`` o fst o strip_comb o lhs))) >>
     first_assum(match_exists_tac o concl) >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_char)` by rw [check_t_def] >>
     metis_tac[t_unify_check_s, t_unify_wfs, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``t_unify`` o fst o strip_comb o lhs))) >>
     first_assum(match_exists_tac o concl) >>
     metis_tac[t_unify_check_s, t_unify_wfs, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [Infer_Tapp [] TC_char] (TC_name (Short "list")))` by rw [check_t_def] >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     metis_tac[check_t_more2, arithmeticTheory.ADD_0])
 >- (`check_t 0 (count (st.next_uvar + 1)) h`
                    by metis_tac [EVERY_DEF, check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_s tvs (count (st.next_uvar+1)) st.subst`
            by metis_tac [check_s_more] >>
     match_mp_tac t_unify_check_s >>
     qexists_tac `st.subst` >>
     rw [] >>
     `check_t tvs (count (st.next_uvar + 1))
                  (Infer_Tapp [Infer_Tuvar st.next_uvar] (TC_name (Short "list")))`
                       by (rw [check_t_def]) >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     rw []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_vector`] >>
         rw []
         >- metis_tac [check_s_more]
         >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
         >- rw [check_t_def])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_vector`] >>
     rw []
     >- metis_tac [check_s_more]
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
     >- rw [check_t_def])
 >- (`check_s tvs (count st.next_uvar) s`
            by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     rw []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_array`] >>
         rw []
         >- metis_tac [check_s_more]
         >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
         >- rw [check_t_def])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE
     ``x ≤ x + 1:num``])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [Infer_Tuvar st.next_uvar] TC_array`] >>
     rw []
     >- metis_tac [check_s_more]
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]
     >- rw [check_t_def])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`s`, `h'`, `Infer_Tapp [] TC_int`] >>
     rw []
     >- metis_tac [t_unify_wfs]
     >- (match_mp_tac t_unify_check_s >>
         MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [h''] TC_array`] >>
         rw [check_t_def] >>
         metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``])
     >- metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``])
 >- (match_mp_tac t_unify_check_s >>
     MAP_EVERY qexists_tac [`st.subst`, `h`, `Infer_Tapp [] TC_word8array`] >>
     rw [] >>
     metis_tac [check_t_more2, check_t_more4, arithmeticTheory.ADD_0, DECIDE ``x ≤ x + 1:num``]));

val ienv_ok_def = Define `
  ienv_ok uvars ienv ⇔
    ienv_val_ok uvars ienv.inf_v ∧
    tenv_ctor_ok ienv.inf_c ∧
    tenv_abbrev_ok ienv.inf_t`;

val ienv_ok_more = Q.store_thm ("ienv_ok_more",
  `!uv uv' ienv. ienv_ok (count uv) ienv ∧ uv ≤ uv' ⇒ ienv_ok (count uv') ienv`,
 rw [ienv_ok_def, ienv_val_ok_def]
 >> metis_tac [check_env_more]);

val infer_e_check_s = Q.store_thm ("infer_e_check_s",
`(!ienv e st st' t tvs.
    infer_e ienv e st = (Success t, st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!ienv es st st' ts tvs.
    infer_es ienv es st = (Success ts, st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!ienv pes t1 t2 st st' tvs.
    infer_pes ienv pes t1 t2 st = (Success (), st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_t 0 (count st.next_uvar) t1 ∧
    check_t 0 (count st.next_uvar) t2 ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst) ∧
 (!ienv funs st st' ts' tvs.
    infer_funs ienv funs st = (Success ts', st') ∧
    t_wfs st.subst ∧
    ienv_ok (count st.next_uvar) ienv ∧
    check_s tvs (count st.next_uvar) st.subst
    ⇒
    check_s tvs (count st'.next_uvar) st'.subst)`,
 ho_match_mp_tac infer_e_ind
 >> rw [infer_e_def, success_eqns]
 >> rw []
 >- (
   drule (CONJUNCT1 infer_e_wfs)
   >> rw []
   >> irule check_s_more
   >> irule t_unify_check_s
   >> HINT_EXISTS_TAC
   >> qexists_tac `t2`
   >> qexists_tac `Infer_Tapp [] TC_exn`
   >> rw [check_t_def]
   >> metis_tac [ienv_ok_def, infer_e_check_t, arithmeticTheory.ADD_0, check_t_more2])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> simp []
   >> rw []
   >> first_x_assum irule
   >> simp [check_t_def]
   >- metis_tac [infer_e_wfs]
   >- metis_tac [ienv_ok_more, infer_e_next_uvar_mono]
   >- metis_tac [check_t_more4, infer_e_next_uvar_mono, infer_e_check_t, ienv_ok_def])
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rw []
   >> metis_tac [check_s_more2, DECIDE ``x ≤ (y:num) + x``])
 >- metis_tac [check_s_more2, DECIDE ``x ≤ x + y:num``]
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rw []
   >> first_x_assum drule
   >> simp []
   >> disch_then drule
   >> rw []
   >> drule pure_add_constraints_check_s
   >> simp []
   >> disch_then irule
   >> simp []
   >- metis_tac [infer_e_wfs]
   >- (
     drule (List.nth (CONJUNCTS infer_e_check_t, 1))
     >> rfs [ienv_ok_def]
     >> fs [EVERY_MEM]
     >> rw []
     >> rfs [MEM_ZIP, LENGTH_COUNT_LIST, EL_MAP]
     >> rw []
     >> fs [MEM_EL, PULL_EXISTS]
     >> rfs []
     >> qpat_x_assum `_ + _ = (_:num)` (assume_tac o GSYM)
     >- (
       first_x_assum drule
       >> rw []
       >> fs []
       >> drule (CONJUNCT1 check_t_more2)
       >> fs []
       >> metis_tac [check_t_more4, DECIDE ``x ≤ y+x:num``])
     >- (
       drule tenv_ctor_ok_lookup
       >> disch_then drule
       >> rw [EVERY_MEM, MEM_EL, PULL_EXISTS]
       >> first_x_assum drule
       >> rw []
       >> drule (CONJUNCT1 check_infer_type_subst)
       >> disch_then (qspec_then `st''.next_uvar` mp_tac)
       >> rw []
       >> drule (CONJUNCT1 check_t_more2)
       >> rw []))
   >- (
     `st''.next_uvar ≤ st'.next_uvar` by decide_tac
     >> metis_tac [check_s_more2]))
 >- (
   first_x_assum drule
   >> simp []
   >> disch_then irule
   >- (
     fs [ienv_ok_def, ienv_val_ok_def]
     >> irule nsAll_nsBind
     >> simp [check_t_def]
     >> irule check_env_more
     >> HINT_EXISTS_TAC
     >> simp [])
   >> metis_tac [check_s_more])
 >- (
   drule (List.nth (CONJUNCTS infer_e_wfs, 1))
   >> rw []
   >> drule constrain_op_check_s
   >> disch_then irule
   >> simp []
   >> metis_tac [infer_e_check_t, ienv_ok_def])
 >- (
   first_x_assum drule
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> drule t_unify_check_s
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> drule t_unify_check_s
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_check_t)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> qpat_x_assum `infer_e _ _ _ = _` mp_tac
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> rw [check_t_def]
   >> first_x_assum irule
   >- metis_tac [t_unify_wfs]
   >- (
     first_x_assum irule
     >- (
       first_x_assum irule
       >> rw []
       >> metis_tac [ienv_ok_more, ienv_ok_def])
     >> metis_tac [check_t_more4, check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])
   >> metis_tac [ienv_ok_more, ienv_ok_def, check_t_more4, check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])
 >- (
   first_x_assum drule
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> drule t_unify_check_s
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> drule t_unify_check_s
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_check_t)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> qpat_x_assum `infer_e _ _ _ = _` mp_tac
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> drule (CONJUNCT1 infer_e_check_t)
   >> qpat_x_assum `infer_e _ _ _ = _` mp_tac
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> rw [check_t_def]
   >> first_x_assum irule
   >- metis_tac [t_unify_wfs]
   >- (
     first_x_assum irule
     >> simp []
     >- metis_tac [t_unify_wfs]
     >- metis_tac [ienv_ok_more, ienv_ok_def]
     >- (
       first_x_assum irule
       >> rw []
       >- metis_tac [t_unify_wfs]
       >- metis_tac [ienv_ok_more, ienv_ok_def]
       >- (
         first_x_assum irule
         >> simp []
         >> metis_tac [check_t_more2, DECIDE ``0n ≤ x ∧ y + 0n = y``])))
   >> metis_tac [ienv_ok_more, ienv_ok_def, check_t_more4, check_t_more2,
                 DECIDE ``0n ≤ x ∧ y + 0n = y``])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> rw [check_t_def]
   >> first_x_assum irule
   >> rw []
   >- metis_tac [infer_e_wfs]
   >- metis_tac [infer_e_next_uvar_mono, ienv_ok_more, DECIDE ``x ≤ x+1n``]
   >- metis_tac [check_s_more]
   >> drule (CONJUNCT1 infer_e_check_t)
   >> fs [ienv_ok_def]
   >> metis_tac [check_t_more3])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> rw [check_t_def]
   >> first_x_assum irule
   >> rw []
   >- metis_tac [infer_e_wfs]
   >> drule ienv_ok_more
   >> disch_then (qspec_then `st''.next_uvar` mp_tac)
   >> rw []
   >> fs [ienv_ok_def, ienv_val_ok_def]
   >> irule nsAll_nsOptBind
   >> rw []
   >> metis_tac [infer_e_check_t, ienv_val_ok_def, infer_e_next_uvar_mono,
                 option_nchotomy, infer_e_wfs])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e (ienv with inf_v := nsAppend bindings ienv.inf_v) _ _ = _`
   >> `ienv_ok (count (LENGTH funs + st.next_uvar)) (ienv with inf_v := nsAppend bindings ienv.inf_v)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsAppend
       >> rw []
       >- (
         irule check_env_letrec_lem
         >> disj2_tac
         >> decide_tac)
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more4, DECIDE ``y ≤ x+y:num``])
   >> rw []
   >> first_x_assum irule
   >> rw []
   >- (
     drule (List.nth (CONJUNCTS infer_e_wfs, 3))
     >> simp []
     >> metis_tac [pure_add_constraints_wfs])
   >- (
     irule ienv_ok_more
     >> HINT_EXISTS_TAC
     >> rw []
     >> drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
     >> rw [])
   >> drule pure_add_constraints_check_s
   >> disch_then irule
   >- (
     drule (List.nth (CONJUNCTS infer_e_wfs, 3))
     >> rw [])
   >- (
     fs [EVERY_MEM, LENGTH_COUNT_LIST, LENGTH_MAP, MEM_ZIP]
     >> rw []
     >> rw [EL_MAP, LENGTH_COUNT_LIST, check_t_def]
     >> drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
     >> rw [EL_COUNT_LIST]
     >> drule (List.nth (CONJUNCTS infer_e_check_t, 3))
     >> rfs [ienv_ok_def]
     >> rw [EVERY_MEM, MEM_EL, PULL_EXISTS]
     >> metis_tac [check_t_more2, DECIDE ``x+0n = x``, MEM_EL])
   >> first_x_assum irule
   >> rw []
   >> metis_tac [check_s_more2, DECIDE ``x ≤ y+x:num``])
 >- (
   drule (CONJUNCT1 infer_e_wfs)
   >> first_x_assum drule
   >> rw []
   >> drule t_unify_check_s
   >> simp []
   >> disch_then irule
   >> simp []
   >- (
     drule (CONJUNCT1 infer_e_check_t)
     >> fs [ienv_ok_def]
     >> metis_tac [check_t_more2, DECIDE ``y + 0n = y``])
   >> fs [ienv_ok_def]
   >> imp_res_tac check_freevars_type_name_subst
   >> drule (CONJUNCT1 infer_type_subst_empty_check)
   >> rw []
   >> metis_tac [COUNT_ZERO, check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y ∧ 0n ≤ y``])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> rw []
   >> first_x_assum irule
   >> metis_tac [infer_e_wfs, ienv_ok_more, infer_e_next_uvar_mono])
 >- (
   pairarg_tac
   >> fs [success_eqns]
   >> rename1 `infer_p _ _ _ = (Success (t1',bindings1),st1)`
   >> drule (REWRITE_RULE [Once CONJ_SYM] (CONJUNCT1 infer_p_wfs))
   >> rw []
   >> drule (CONJUNCT1 infer_p_check_t)
   >> rw []
   >> drule (CONJUNCT1 infer_p_next_uvar_mono)
   >> drule (CONJUNCT1 infer_p_check_s)
   >> `tenv_ctor_ok ienv.inf_c ∧ tenv_abbrev_ok ienv.inf_t` by fs [ienv_ok_def]
   >> simp []
   >> disch_then drule
   >> rw []
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> rename1 `t_unify _ t1 t1' = SOME s1`
   >> drule (REWRITE_RULE [Once CONJ_SYM] t_unify_wfs)
   >> drule t_unify_check_s
   >> rpt (disch_then drule)
   >> `check_t tvs (count st1.next_uvar) t1 ∧ check_t tvs (count st1.next_uvar) t1'`
     by metis_tac [check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y``]
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e (ienv with inf_v := nsAppend bindings2 ienv.inf_v) _ _ = (Success t2', st2)`
   >> `ienv_val_ok (count st1.next_uvar) (nsAppend bindings2 ienv.inf_v)`
     by (
       fs [ienv_ok_def, ienv_val_ok_def, Abbr `bindings2`]
       >> irule nsAll_nsAppend
       >- (
         irule nsAll_alist_to_ns
         >> fs [EVERY_MAP, EVERY_MEM]
         >> rw []
         >> rpt (pairarg_tac >> fs [])
         >> rw []
         >> first_x_assum drule
         >> rw [])
       >- (
         irule nsAll_mono
         >> HINT_EXISTS_TAC
         >> rw []
         >> rpt (pairarg_tac >> fs [])
         >> metis_tac [check_t_more4]))
   >> drule (CONJUNCT1 infer_e_check_t)
   >> simp []
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_e_wfs)
   >> simp [ienv_ok_def]
   >> rw []
   >> rename1 `t_unify _ t2 t2' = SOME s2`
   >> drule (REWRITE_RULE [Once CONJ_SYM] t_unify_wfs)
   >> drule t_unify_check_s
   >> simp []
   >> rpt (disch_then drule)
   >> `check_t tvs (count st2.next_uvar) t2 ∧ check_t tvs (count st2.next_uvar) t2'`
     by metis_tac [check_t_more2, check_t_more4, DECIDE ``!y. y + 0n = y``]
   >> rw []
   >> first_x_assum drule
   >> simp []
   >> disch_then irule
   >> simp []
   >- metis_tac [ienv_ok_more]
   >- (
     fs [Abbr `bindings2`]
     >> first_x_assum drule
     >> simp [ienv_ok_def])
   >- metis_tac [check_t_more4]
   >- metis_tac [check_t_more4])
 >- (
   first_x_assum drule
   >> first_x_assum drule
   >> rw []
   >> qmatch_assum_abbrev_tac `infer_e (ienv with inf_v := bindings) _ _ = _`
   >> `ienv_ok (count (st.next_uvar+1)) (ienv with inf_v := bindings)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsBind
       >> simp [check_t_def]
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more3])
   >> first_x_assum irule
   >- (
     drule (CONJUNCT1 infer_e_wfs)
     >> rw [])
   >- (
     drule (CONJUNCT1 infer_e_next_uvar_mono)
     >> rw []
     >> metis_tac [ienv_ok_more, DECIDE ``x ≤ x+1n``])
   >> first_x_assum irule
   >> simp [check_s_more]));

val generalise_complete_lemma = Q.prove (
`!tvs ts.
  (∀uv. uv ∈ FDOM (FEMPTY |++ ts) ⇒ ∃tv. (FEMPTY |++ ts) ' uv = tv ∧ tv < tvs)
  ⇒
  (∀uv. uv ∈ FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ⇒ ∃tv. (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) ' uv = Infer_Tvar_db tv ∧ tv < tvs)`,
rw [FDOM_FUPDATE_LIST, MEM_MAP] >>
PairCases_on `y'` >>
fs [] >>
`y'0 ∈ FDOM (FEMPTY |++ ts)`
        by (rw [FDOM_FUPDATE_LIST, MEM_MAP] >> metis_tac [FST]) >>
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
rw [pure_add_constraints_def, FUPDATE_LIST_THM] >>
PairCases_on `h` >>
rw [pure_add_constraints_def] >>
`t_unify s (Infer_Tuvar h0) h1 = SOME (s |+ (h0,h1))`
           by (rw [t_unify_eqn] >>
               rw [Once t_walk_eqn] >>
               rw [Once t_vwalk_eqn, FLOOKUP_DEF] >|
               [fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
                    metis_tac [],
                fs [] >>
                    rw [t_walk_eqn, t_ext_s_check_eqn, oc_tvar_db, oc_unit]]) >>
`t_wfs (s |+ (h0,h1))` by metis_tac [t_unify_wfs] >>
qexists_tac `s |+ (h0,h1)` >>
rw [] >>
`DISJOINT (FDOM (s |+ (h0,h1))) (FDOM (FEMPTY |++ ts))`
         by (fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
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
 rw [] >>
 imp_res_tac t_vwalk_eqn >>
 ONCE_ASM_REWRITE_TAC [] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 fs [flookup_fupdate_list, infer_subst_var_def] >>
 every_case_tac >>
 fs [infer_subst_var_def, flookup_fupdate_list] >>
 every_case_tac >>
 fs [ALOOKUP_FAILS, PROVE [flookup_thm] ``FLOOKUP f x = NONE ⇔ x ∉ FDOM f``] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11]
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
         combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD] >>
     metis_tac [])
 >- (fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MAP_MAP_o,
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
 rw [] >>
 cases_on `t` >>
 rw [t_walkstar_eqn, t_walk_eqn, infer_subst_def] >>
 fs [t_walk_eqn]
 >- (induct_on `l` >>
     rw []) >>
 `infer_subst_var (FEMPTY |++ s') (t_vwalk s n) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n`
          by metis_tac [generalise_complete_lemma4] >>
 cases_on `t_vwalk s n` >>
 rw [] >>
 cases_on `t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n` >>
 rw [] >>
 fs [infer_subst_def, infer_subst_var_def] >>
 rw [MAP_MAP_o, MAP_EQ_f] >>
 cases_on `FLOOKUP (FEMPTY |++ s') n'` >>
 fs []);

val fst_lem = Q.prove (
`FST = (\(x,y).x)`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
rw []);

val generalise_complete = Q.store_thm ("generalise_complete",
`!n s l tvs s' ts next_uvar.
  generalise_list 0 n FEMPTY (MAP (t_walkstar s) l) = (tvs,s',ts) ∧
  t_wfs s ∧
  check_s 0 (count next_uvar) s ∧
  EVERY (\t. check_t 0 (count next_uvar) t) l
  ⇒
  ?ec1 last_sub.
    (ts = MAP (t_walkstar last_sub) l) ∧
    t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub`,
rw [] >>
imp_res_tac generalise_subst_empty >>
rw [sub_completion_def] >>
Q.ABBREV_TAC `unconstrained = count next_uvar DIFF (FDOM s ∪ FDOM s')` >>
`?ts. ALL_DISTINCT (MAP FST ts) ∧ s' = FEMPTY |++ ts` by metis_tac [fmap_to_list] >>
rw [] >>
`FINITE unconstrained` by metis_tac [FINITE_COUNT, FINITE_DIFF, FINITE_UNION, finite_t_rangevars] >>
`?ts2. ALL_DISTINCT (MAP FST ts2) ∧ FEMPTY |++ ts2 = (FUN_FMAP (\x. Infer_Tapp [] TC_unit) unconstrained)` by metis_tac [fmap_to_list] >>
`DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts2))`
             by (rw [EXTENSION, DISJOINT_DEF] >>
                 Q.UNABBREV_TAC `unconstrained` >>
                 rw [] >>
                 CCONTR_TAC >>
                 fs [] >>
                 fs []) >>
`DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))`
             by (rw [] >>
                 fs [MEM_MAP] >>
                 rw [EXTENSION, DISJOINT_DEF] >>
                 fs [] >>
                 metis_tac [t_walkstar_vars_notin]) >>
`t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)`
      by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)`
             by (rw [t_vR_eqn, FUN_EQ_THM] >>
                 every_case_tac >>
                 fs [flookup_fupdate_list] >>
                 every_case_tac >>
                 fs [] >>
                 imp_res_tac ALOOKUP_MEM >>
                 fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, t_vars_eqn] >>
                 fs [flookup_thm, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MEM_MAP] >>
                 metis_tac [pair_CASES, FST]) >>
         fs [t_vars_eqn, t_wfs_eqn]) >>
`t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
      by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
             by (rw [t_vR_eqn, FUN_EQ_THM] >>
                 cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) x'` >>
                 rw [flookup_update_list_some, flookup_update_list_none] >-
                 fs [flookup_update_list_none] >>
                 pop_assum mp_tac >>
                 rw [flookup_update_list_some] >|
                 [imp_res_tac ALOOKUP_MEM >>
                      pop_assum mp_tac >>
                      rw [MAP_REVERSE] >>
                      `x' ∈ FDOM (FEMPTY |++ ts2)`
                                by metis_tac [MEM_MAP, FDOM_FUPDATE_LIST, IN_UNION, FST, pair_CASES] >>
                      `x' ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s x' = NONE` by metis_tac [FLOOKUP_DEF] >>
                      rw [] >>
                      `FLOOKUP (FEMPTY |++ ts2) x' = SOME x''` by rw [flookup_update_list_some] >>
                      pop_assum mp_tac >>
                      rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                      rw [FLOOKUP_FUN_FMAP, t_vars_eqn],
                 imp_res_tac ALOOKUP_MEM >>
                      pop_assum mp_tac >>
                      rw [MEM_MAP, MAP_REVERSE] >>
                      PairCases_on `y` >>
                      rw [] >>
                      `MEM y0 (MAP FST ts)` by (rw [MEM_MAP] >> metis_tac [FST]) >>
                      `y0 ∈ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                      `y0 ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s y0 = NONE` by metis_tac [FLOOKUP_DEF] >>
                      rw [] >>
                      fs [] >>
                      `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) y0 = SOME x''` by rw [flookup_update_list_some] >>
                      imp_res_tac ALOOKUP_MEM >>
                      fs [MEM_MAP] >>
                      rw [] >>
                      PairCases_on `y'` >>
                      rw [] >>
                      rw [t_vars_eqn, encode_infer_t_def],
                  rw []]) >>
         fs [t_vars_eqn, t_wfs_eqn]) >>
`count next_uvar ⊆ FDOM (s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2)`
      by (rw [FDOM_FUPDATE_LIST, SUBSET_DEF] >>
          CCONTR_TAC >>
          fs [] >>
          `x ∉ FDOM (FEMPTY |++ ts2)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
          pop_assum mp_tac >>
          rw [FLOOKUP_FUN_FMAP] >>
          `x ∉ set (MAP FST ts)` by metis_tac [map_fst] >>
          `x ∉ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, FDOM_FEMPTY, NOT_IN_EMPTY] >>
          Q.UNABBREV_TAC `unconstrained` >>
          rw []) >>
`DISJOINT (FDOM (FEMPTY |++ ts)) (FDOM (FEMPTY |++ ts2))`
             by (Q.UNABBREV_TAC `unconstrained` >>
                 rw [DISJOINT_DEF, EXTENSION] >>
                 metis_tac []) >>
qexists_tac `(MAP (\(uv,tv). (Infer_Tuvar uv, Infer_Tvar_db tv)) ts) ++
             (MAP (\(uv,t). (Infer_Tuvar uv, t)) ts2)` >>
qexists_tac `s |++ (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts) |++ ts2` >>
rw [] >|
[rw [MAP_EQ_f, MAP_MAP_o] >>
     `DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts))`
               by (fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, map_fst] >>
                   metis_tac []) >>
     `infer_subst (FEMPTY |++ ts) (t_walkstar s e) = t_walkstar (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) e`
               by metis_tac [generalise_complete_lemma5] >>
     rw [] >>
     fs [] >>
     rw [] >>
     fs [] >>
     `(t_vars o infer_subst (FEMPTY |++ ts) o t_walkstar s) e = {}`
             by metis_tac [no_vars_lem, MAP_MAP_o] >>
     fs [combinTheory.o_DEF] >>
     pop_assum mp_tac >>
     rw [] >>
     `DISJOINT (FDOM (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) (FDOM (FEMPTY |++ ts2))`
                by (rw [FDOM_FUPDATE_LIST, map_fst] >>
                    fs [FDOM_FUPDATE_LIST]) >>
     metis_tac [no_vars_extend_subst],
 `MAP (λ(uv,tv). (Infer_Tuvar uv,Infer_Tvar_db tv)) ts ++ MAP (λ(uv,t). (Infer_Tuvar uv,t)) ts2
  =
  MAP (λ(uv,t). (Infer_Tuvar uv, t)) (MAP (\(uv,tv). (uv, Infer_Tvar_db tv)) ts ++ ts2)`
            by rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
     ASM_REWRITE_TAC [GSYM FUPDATE_LIST_APPEND] >>
     match_mp_tac generalise_complete_lemma2 >>
     rw [MAP_MAP_o, EVERY_MAP, LAMBDA_PROD, ALL_DISTINCT_APPEND, combinTheory.o_DEF] >|
     [metis_tac [fst_lem],
      `e ∈ FDOM (FEMPTY |++ ts)`
                   by metis_tac [FDOM_FUPDATE_LIST, IN_UNION, fst_lem] >>
          `e ∉ unconstrained`
                   by (Q.UNABBREV_TAC `unconstrained` >>
                       fs []) >>
          `e ∉ FDOM (FEMPTY |++ ts2)`
                    by metis_tac [FDOM_FMAP] >>
          fs [FDOM_FUPDATE_LIST],
      rw [EVERY_MEM] >>
          PairCases_on `e` >>
          rw [],
      rw [EVERY_MEM] >>
          PairCases_on `e` >>
          rw [] >>
          `FLOOKUP (FEMPTY |++ ts2) e0 = SOME e1`
                    by (rw [flookup_fupdate_list] >>
                        full_case_tac >>
                        fs [ALOOKUP_FAILS] >>
                        metis_tac [optionTheory.SOME_11,ALOOKUP_ALL_DISTINCT_MEM, MEM_REVERSE, ALL_DISTINCT_REVERSE, REVERSE_REVERSE, MAP_REVERSE]) >>
          pop_assum mp_tac >>
          rw [FLOOKUP_FUN_FMAP],
      fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST] >>
          rw [map_fst] >>
          metis_tac []],
 ONCE_REWRITE_TAC [GSYM COUNT_ZERO] >>
     match_mp_tac t_walkstar_check >>
     rw [check_t_def, check_s_def] >>
     `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) uv' = SOME ((s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) ' uv')`
                    by rw [FLOOKUP_DEF] >>
     pop_assum mp_tac >>
     rw [flookup_update_list_some] >>
     Q.ABBREV_TAC `last_sub = s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2` >|
     [`FLOOKUP (FEMPTY |++ ts2) uv' = SOME (last_sub ' uv')` by metis_tac [flookup_update_list_some] >>
          pop_assum mp_tac >>
          rw [FLOOKUP_FUN_FMAP] >>
          metis_tac [check_t_def, EVERY_DEF],
      `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) uv' = SOME (last_sub ' uv')`
                    by metis_tac [flookup_update_list_some] >>
          `(!uv. uv ∈ FDOM (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ⇒ ∃tv. (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ' uv = Infer_Tvar_db tv ∧ tv < tvs + n)`
                   by metis_tac [generalise_complete_lemma] >>
          fs [FLOOKUP_DEF] >>
          metis_tac [check_t_def],
      fs [check_s_def, FLOOKUP_DEF] >>
          metis_tac [check_t_more2, check_t_more5, arithmeticTheory.ADD_0]]]);

val init_infer_state_wfs = Q.prove (
  `t_wfs init_infer_state.subst ∧
   check_s 0 ∅ init_infer_state.subst`,
 rw [check_s_def, init_infer_state_def, t_wfs_def]);

val init_infer_state_next_uvar = Q.store_thm ("init_infer_state_next_uvar[simp]",
  `init_infer_state.next_uvar = 0`,
 rw [init_infer_state_def]);

val let_tac =
   drule (CONJUNCT1 infer_e_check_t)
   >> drule (CONJUNCT1 infer_e_check_s)
   >> simp []
   >> disch_then drule
   >> drule (CONJUNCT1 infer_e_wfs)
   >> drule (CONJUNCT1 infer_p_check_t)
   >> fs [ienv_ok_def]
   >> rw []
   >> drule (CONJUNCT1 infer_p_check_s)
   >> simp []
   >> disch_then drule
   >> rw []
   >> drule (CONJUNCT1 infer_p_wfs)
   >> disch_then drule
   >> rw []
   >> drule t_unify_check_s
   >> rpt (disch_then drule)
   >> drule (CONJUNCT1 infer_e_next_uvar_mono)
   >> drule (CONJUNCT1 infer_p_next_uvar_mono)
   >> rw []
   >> rename1 `infer_p _ _ st2 = (Success (t2, env2), st3)`
   >> `check_t 0 (count st3.next_uvar) t1` by metis_tac [check_t_more4]
   >> fs []
   >> drule t_unify_wfs
   >> disch_then drule
   >> rw []
   >> drule generalise_complete
   >> rpt (disch_then drule)
   >> fs [every_shim]
   >> rw [ienv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> simp [EVERY_MEM, MEM_ZIP]
   >> rw []
   >> rw [EL_MAP]
   >> irule (CONJUNCT1 check_t_walkstar)
   >> simp []
   >> fs [sub_completion_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
   >> metis_tac [check_t_more2, check_t_more5, MEM_EL, DECIDE ``x + 0n = x``];

val eta2_thm = Q.prove (
`(\x. f a b x) = f a b`, metis_tac []);

val check_env_letrec_lem2 = Q.prove (
  `∀funs.
    nsAll (λx (tvs,t). check_t tvs (count (LENGTH funs)) t)
      (alist_to_ns (MAP2 (λ(f,x,e) uvar. (f,0,uvar))
                      funs
                      (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))`,
 rw []
 >> Q.SPECL_THEN [`LENGTH funs`, `funs`, `0n`] mp_tac check_env_letrec_lem
 >> simp []);

val infer_d_check = Q.store_thm ("infer_d_check",
`!mn decls1 ienv d st1 st2 decls' ienv'.
  infer_d mn decls1 ienv d st1 = (Success (decls',ienv'), st2) ∧
  ienv_ok {} ienv
  ⇒
  ienv_ok {} ienv'`,
 cases_on `d`
 >> rpt gen_tac
 >> strip_tac
 >> fs [infer_d_def, success_eqns]
 >> rpt (pairarg_tac >> fs [success_eqns])
 >> fs [init_state_def]
 >> rw []
 >> strip_assume_tac init_infer_state_wfs
 >- let_tac
 >- let_tac
 >- (
   qmatch_assum_abbrev_tac
     `infer_funs (ienv with inf_v := nsAppend bindings ienv.inf_v) _ _ = _`
   >> rename1 `infer_funs _ funs _ = (Success funs_ts, st1)`
   >> rename1 `pure_add_constraints _ _ st2.subst`
   >> `ienv_ok (count (LENGTH funs)) (ienv with inf_v := nsAppend bindings ienv.inf_v)`
     by (
       fs [ienv_ok_def, Abbr `bindings`, ienv_val_ok_def]
       >> irule nsAll_nsAppend
       >> simp []
       >- metis_tac [check_env_letrec_lem2]
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more4, COUNT_ZERO, DECIDE ``0n≤ x``])
   >> `check_s 0 (count (LENGTH funs)) init_infer_state.subst`
     by rw [init_infer_state_def, check_s_def]
   >> drule (List.nth (CONJUNCTS infer_e_check_t, 3))
   >> drule (List.nth (CONJUNCTS infer_e_wfs, 3))
   >> fs [ienv_ok_def]
   >> drule (List.nth (CONJUNCTS infer_e_check_s, 3))
   >> simp [ienv_ok_def]
   >> disch_then drule
   >> rw []
   >> drule (List.nth (CONJUNCTS infer_e_next_uvar_mono, 3))
   >> simp [ienv_ok_def]
   >> drule pure_add_constraints_wfs
   >> rw []
   >> `EVERY (\t. check_t 0 (count st2.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))`
      by rw [EVERY_MAP, every_count_list, check_t_def]
   >> drule pure_add_constraints_check_s
   >> fs [every_zip_split, eta2_thm, ETA_THM]
   >> simp [GSYM CONJ_ASSOC]
   >> rpt (disch_then drule)
   >> rw []
   >> drule generalise_complete
   >> simp [eta2_thm]
   >> rpt (disch_then drule)
   >> rw [ienv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> rw [EVERY_MEM, MEM_ZIP]
   >> pairarg_tac
   >> rw []
   >> pairarg_tac
   >> rw []
   >> fs [MAP2_MAP, LENGTH_COUNT_LIST, MEM_MAP, MEM_ZIP, MAP_MAP_o, combinTheory.o_DEF]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> rw [EL_MAP, LENGTH_COUNT_LIST]
   >> irule (CONJUNCT1 check_t_walkstar)
   >> simp []
   >> fs [sub_completion_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
   >> rw [check_t_def, EL_COUNT_LIST]
   >> fs [SUBSET_DEF])
 >- (
   simp [ienv_ok_def]
   >> conj_tac
   >- rw [ienv_val_ok_def]
   >> conj_asm2_tac
   >- (
     irule check_ctor_tenv_ok
     >> fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def, ienv_ok_def]
     >> irule nsAll_nsAppend
     >> simp [])
   >> fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def]
   >> irule nsAll_alist_to_ns
   >> rw [EVERY_MAP, EVERY_MEM]
   >> rpt (pairarg_tac >> fs [])
   >> fs []
   >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (
   rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_abbrev_ok_def]
   >> irule check_freevars_type_name_subst
   >> fs [ienv_ok_def])
 >- (
   fs [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
       EVERY_MAP, EVERY_MEM, MEM_MAP]
   >> rw []
   >> irule check_freevars_type_name_subst
   >> fs [check_exn_tenv_def, EVERY_MEM]));

val ienv_ok_extend_dec_ienv = Q.store_thm ("ienv_ok_extend_dec_ienv",
  `!e1 e2 n. ienv_ok n e1 ∧ ienv_ok n e2 ⇒ ienv_ok n (extend_dec_ienv e1 e2)`,
 rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
     typeSoundInvariantsTheory.tenv_abbrev_ok_def, extend_dec_ienv_def]
 >> metis_tac [nsAll_nsAppend]);

val infer_ds_check = Q.store_thm ("infer_ds_check",
  `!mn decls ienv ds st1 st2 decls' ienv'.
    infer_ds mn decls ienv ds st1 = (Success (decls', ienv'), st2) ∧
    ienv_ok {} ienv
    ⇒
    ienv_ok {} ienv'`,
 induct_on `ds` >>
 rw [infer_ds_def, success_eqns]
 >- rw [ienv_ok_def, ienv_val_ok_def]
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [success_eqns]
 >> rpt (pairarg_tac >> fs [])
 >> rw []
 >> fs [success_eqns]
 >> rw []
 >> drule infer_d_check
 >> first_x_assum drule
 >> rw []
 >> metis_tac [ienv_ok_extend_dec_ienv]);

val count_list_one = Q.prove (
`COUNT_LIST 1 = [0]`,
metis_tac [COUNT_LIST_def, MAP, DECIDE ``1 = SUC 0``]);

val check_freevars_more_append = Q.prove (
`(!t x fvs1 fvs2.
  check_freevars x fvs1 t ⇒
  check_freevars x (fvs2++fvs1) t ∧
  check_freevars x (fvs1++fvs2) t) ∧
 (!ts x fvs1 fvs2.
  EVERY (check_freevars x fvs1) ts ⇒
  EVERY (check_freevars x (fvs2++fvs1)) ts ∧
  EVERY (check_freevars x (fvs1++fvs2)) ts)`,
Induct >>
rw [check_freevars_def] >>
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
rw [t_to_freevars_def, success_eqns, check_freevars_def] >>
rw [] >>
metis_tac [check_freevars_more_append]);

val check_freevars_more = store_thm("check_freevars_more",
  ``∀a b c. check_freevars a b c ⇒ ∀b'. set b ⊆ set b' ⇒ check_freevars a b' c``,
  ho_match_mp_tac check_freevars_ind >>
  rw[check_freevars_def] >-
    fs[SUBSET_DEF] >>
  fs[EVERY_MEM])

val check_freevars_t_to_freevars = store_thm("check_freevars_t_to_freevars",
  ``(∀t fvs (st:'a). check_freevars 0 fvs t ⇒
      ∃fvs' st'. t_to_freevars t st = (Success fvs', st') ∧ set fvs' ⊆ set fvs) ∧
    (∀ts fvs (st:'a). EVERY (check_freevars 0 fvs) ts ⇒
      ∃fvs' st'. ts_to_freevars ts st = (Success fvs', st') ∧ set fvs' ⊆ set fvs)``,
  Induct >> simp[check_freevars_def,t_to_freevars_def,PULL_EXISTS,success_eqns] >>
  simp_tac(srw_ss()++boolSimps.ETA_ss)[] >> simp[] >> metis_tac[])

val check_t_infer_type_subst_dbs = store_thm("check_t_infer_type_subst_dbs",
  ``∀m w t n u ls.
    check_freevars m w t ∧
    m + LENGTH ls ≤ n ∧
    (ls = [] ⇒ 0 < m)
    ⇒
    check_t n u (infer_type_subst (ZIP(ls,MAP Infer_Tvar_db (COUNT_LIST (LENGTH ls)))) t)``,
  ho_match_mp_tac check_freevars_ind >>
  conj_tac >- (
    simp[check_freevars_def] >>
    simp[infer_type_subst_def] >>
    simp[ZIP_MAP,LENGTH_COUNT_LIST] >>
    simp[ALOOKUP_MAP,LAMBDA_PROD] >>
    simp[COUNT_LIST_GENLIST] >>
    simp[ZIP_GENLIST] >>
    rw[] >>
    BasicProvers.CASE_TAC >- (
      simp[check_t_def] >>
      Cases_on`LENGTH ls = 0`>-(fs[LENGTH_NIL] >> DECIDE_TAC) >>
      DECIDE_TAC ) >>
    fs[optionTheory.OPTION_MAP_EQ_SOME] >>
    simp[check_t_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_GENLIST] >>
    DECIDE_TAC ) >>
  conj_tac >- (
    rw[check_freevars_def,infer_type_subst_def,check_t_def] >>
    simp[EVERY_MAP] >> fs[EVERY_MEM] ) >>
  rw[check_freevars_def,check_t_def,infer_type_subst_def] >>
  DECIDE_TAC)

val nub_eq_nil = store_thm("nub_eq_nil",
  ``∀ls. nub ls = [] ⇔ ls = []``,
  Induct >> simp[nub_def] >> rw[] >>
  Cases_on`ls`>>fs[])

val check_specs_check = Q.store_thm ("check_specs_check",
`!mn orig_tenvT idecls ienv specs st decls' ienv' st'.
  check_specs mn orig_tenvT idecls ienv specs st = (Success (decls',ienv'), st') ∧
  tenv_abbrev_ok orig_tenvT ∧
  ienv_ok {} ienv
  ⇒
  ienv_ok {} ienv'`,
 ho_match_mp_tac check_specs_ind >>
 STRIP_TAC >>
 REPEAT GEN_TAC >-
 (rw [check_specs_def, success_eqns] >>
  metis_tac []) >>
 REPEAT CONJ_TAC >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
 fs [check_specs_def, success_eqns]
 >-
   (rpt gen_tac>>strip_tac>>
   FIRST_X_ASSUM match_mp_tac >>
   fs[check_specs_def]>>
   qexists_tac`nub fvs`>>fs[GSYM PULL_EXISTS]>>
   CONJ_TAC>- metis_tac []
   >> imp_res_tac t_to_freevars_check>>
     imp_res_tac check_freevars_type_name_subst>>
     Cases_on`fvs = []`>-
       (fs[nub_def,COUNT_LIST_def]>>
       fs [ienv_ok_def, ienv_val_ok_def]
       >> irule nsAll_nsBind
       >> simp []
       >> metis_tac[infer_type_subst_empty_check])
     >>
     fs [ienv_ok_def, ienv_val_ok_def] >>
     irule nsAll_nsBind >>
     simp [] >>
     match_mp_tac check_t_infer_type_subst_dbs>>
     qexists_tac`0`>>
     qexists_tac`fvs`>>
     fs[nub_eq_nil])
 >- (rpt gen_tac >>
     strip_tac >>
     FIRST_X_ASSUM match_mp_tac >>
     rw [] >>
     qmatch_assum_abbrev_tac `check_ctor_tenv (nsAppend new_tenvT orig_tenvT) _`
     >> qexists_tac `nsAppend new_tenvT orig_tenvT`
     >> qexists_tac `MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs`
     >> qexists_tac `new_tenvT`
     >> qexists_tac `st`
     >> simp []
     >> `tenv_abbrev_ok new_tenvT`
       by (
         simp [Abbr `new_tenvT`, typeSoundInvariantsTheory.tenv_abbrev_ok_def]
         >> irule nsAll_alist_to_ns
         >> rw [EVERY_MEM, MEM_MAP]
         >> rpt (pairarg_tac >> fs [])
         >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
     >> conj_asm1_tac
     >- (
       fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def]
       >> irule nsAll_nsAppend
       >> simp [])
     >> fs [ienv_ok_def]
     >> conj_tac
     >- (
       fs [typeSoundInvariantsTheory.tenv_ctor_ok_def]
       >> irule nsAll_nsAppend
       >> simp []
       >> irule (SIMP_RULE (srw_ss()) [typeSoundInvariantsTheory.tenv_ctor_ok_def] check_ctor_tenv_ok)
       >> simp [])
     >- metis_tac [typeSoundInvariantsTheory.tenv_abbrev_ok_def, nsAll_nsAppend])
 >- (
   rw []
   >> first_x_assum match_mp_tac
   >> fs [ienv_ok_def]
   >> `tenv_abbrev_ok (nsSing tn (tvs, type_name_subst orig_tenvT t):tenv_abbrev)`
     by (
       rw [typeSoundInvariantsTheory.tenv_abbrev_ok_def]
       >> irule check_freevars_type_name_subst
       >> simp [])
   >> metis_tac [typeSoundInvariantsTheory.tenv_abbrev_ok_def, nsAll_nsAppend, nsAppend_nsSing])
 >- (
   rw []
   >> first_x_assum irule
   >> simp []
   >- metis_tac []
   >> fs [ienv_ok_def, check_exn_tenv_def, typeSoundInvariantsTheory.tenv_ctor_ok_def]
   >> irule nsAll_nsBind
   >> fs [EVERY_MAP, EVERY_MEM]
   >> rw []
   >> fs [MEM_MAP]
   >> metis_tac [check_freevars_type_name_subst])
 >- (
   rw []
   >> first_x_assum irule
   >> `tenv_abbrev_ok ((nsSing tn (tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn)))):tenv_abbrev)`
     by rw [typeSoundInvariantsTheory.tenv_abbrev_ok_def, check_freevars_def, EVERY_MAP, EVERY_MEM]
   >> qmatch_assum_abbrev_tac `tenv_abbrev_ok new_tenvT`
   >> qexists_tac `decls'`
   >> qexists_tac `new_tenvT`
   >> qexists_tac `st`
   >> fs [ienv_ok_def, typeSoundInvariantsTheory.tenv_abbrev_ok_def]
   >> rw [Abbr `new_tenvT`]
   >> irule nsAll_nsBind
   >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM]));

val ienv_ok_lift = Q.store_thm ("ienv_ok_lift",
  `!mn ienv n. ienv_ok n ienv ⇒ ienv_ok n (ienvLift mn ienv)`,
 rw [ienvLift_def, ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
     typeSoundInvariantsTheory.tenv_abbrev_ok_def]);

val infer_top_invariant = Q.store_thm ("infer_top_invariant",
`!decls1 ienv top st1 decls' ienv' st2.
  infer_top decls1 ienv top st1 = (Success (decls', ienv'), st2) ∧
  ienv_ok {} ienv
  ⇒
  ienv_ok {} ienv'`,
 rw []
 >> Cases_on `top`
 >> fs [infer_top_def, success_eqns]
 >> rpt (pairarg_tac >> fs [])
 >> fs [success_eqns]
 >> rpt (pairarg_tac >> fs [])
 >> fs [success_eqns]
 >> rw []
 >- (
   drule infer_ds_check
   >> rw []
   >> rename1 `check_signature [mn] _ _ _ _ si st2 = _`
   >> Cases_on `si`
   >> fs [check_signature_def, success_eqns]
   >> rw []
   >> irule ienv_ok_lift
   >> simp []
   >> rpt (pairarg_tac >> fs [])
   >> rw []
   >> fs [success_eqns]
   >> rw []
   >> drule check_specs_check
   >> disch_then irule
   >> fs [ienv_ok_def, ienv_val_ok_def])
 >> metis_tac [infer_d_check]);

(* ---------- Converting infer types and envs to type system ones ---------- *)

val convert_t_def = tDefine "convert_t" `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`
(WF_REL_TAC `measure infer_t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_tTheory.infer_t_size_def] >>
 res_tac >>
 decide_tac);

val convert_env_def = Define `
convert_env s env = MAP (\(x,t). (x, convert_t (t_walkstar s t))) env`;

val convert_decls_def = Define `
convert_decls idecls =
  <| defined_mods := set idecls.inf_defined_mods;
     defined_types :=  set idecls.inf_defined_types;
     defined_exns := set idecls.inf_defined_exns|>`;

val convert_append_decls = Q.store_thm ("convert_append_decls",
`!decls1 decls2. convert_decls (append_decls decls1 decls2) = union_decls (convert_decls decls1) (convert_decls decls2)`,
 rw [convert_decls_def, append_decls_def, union_decls_def]);

val check_convert_freevars = Q.store_thm ("check_convert_freevars",
`(!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))`,
ho_match_mp_tac check_t_ind >>
rw [check_freevars_def, check_t_def, convert_t_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []);

val check_t_to_check_freevars = Q.store_thm ("check_t_to_check_freevars",
`!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)`,
ho_match_mp_tac check_t_ind >>
rw [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
fs [EVERY_MEM]);

val convert_inc = Q.store_thm ("convert_inc",
`!t tvs tvs'.
  check_t tvs' {} t
  ⇒
  (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
rw [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
induct_on `ts` >>
fs [] >>
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
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST] >|
[`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def,
         LENGTH_COUNT_LIST] >>
     fs [LENGTH_MAP, el_map_count, EL_COUNT_LIST],
 `t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def, MAP_MAP_o,
         combinTheory.o_DEF] >>
     metis_tac [],
 res_tac >>
     imp_res_tac convert_inc >>
     rw [walkstar_inc2] >>
     metis_tac [subst_inc_cancel, arithmeticTheory.ADD,
                deBruijn_inc0,
                LENGTH_COUNT_LIST, LENGTH_MAP],
 metis_tac [],
 metis_tac []]);

val inc_convert_t = Q.store_thm ("inc_convert_t",
`(!t tvs' tvs. check_t tvs' {} t ⇒ (deBruijn_inc tvs' tvs (convert_t t) = convert_t t)) ∧
 (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ⇒ (MAP (deBruijn_inc tvs' tvs o convert_t) ts = MAP convert_t ts))`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, convert_t_def, deBruijn_inc_def] >>
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
rw [check_freevars_def, convert_t_def, type_subst_def, infer_type_subst_def] >|
[full_case_tac >>
     full_case_tac >>
     fs [ALOOKUP_FAILS] >>
     imp_res_tac ALOOKUP_MEM >>
     REPEAT (pop_assum mp_tac) >>
     rw [MAP_ZIP] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`tvs`,`tvs`) >>
     induct_on `ts'` >>
     rw [] >>
     cases_on `tvs` >>
     fs [] >>
     metis_tac [optionTheory.SOME_11],
 metis_tac []]);

val sub_completion_wfs = Q.store_thm ("sub_completion_wfs",
`!n uvars s1 ts s2.
  t_wfs s1 ∧
  sub_completion n uvars s1 ts s2
  ⇒
  t_wfs s2`,
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

val unconvert_t_def = tDefine "unconvert_t" `
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc)`
(wf_rel_tac `measure t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val unconvert_t_ind = theorem"unconvert_t_ind"

val unconvert_t_Tword = Q.store_thm("unconvert_t_Tword[simp]",
  `unconvert_t (Tword wz) = Infer_Tapp [] (TC_word wz)`,
  EVAL_TAC);

val check_freevars_empty_convert_unconvert_id = store_thm("check_freevars_empty_convert_unconvert_id",
``!t. check_freevars n [] t ⇒ convert_t (unconvert_t t) = t``,
  ho_match_mp_tac unconvert_t_ind>>
  rw[]>>fs[unconvert_t_def,convert_t_def,check_freevars_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM])

val check_t_empty_unconvert_convert_id = store_thm("check_t_empty_unconvert_convert_id",
``!t n. check_t n {} t ⇒
  unconvert_t (convert_t t) = t``,
  ho_match_mp_tac (fetch "-" "convert_t_ind") >>
  rw[]>>
  fs[unconvert_t_def,convert_t_def,check_t_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM] >>
  metis_tac []);

val check_freevars_to_check_t = store_thm("check_freevars_to_check_t",
``!t z. check_freevars n [] t ⇒ check_t n {} (unconvert_t t)``,
  ho_match_mp_tac unconvert_t_ind>>rw[]>>
  fs[unconvert_t_def,check_freevars_def,check_t_def]>>
  fs[EVERY_MAP,EVERY_MEM])

val infer_deBruijn_subst_id = store_thm("infer_deBruijn_subst_id",
``(!t. infer_deBruijn_subst [] t = t) ∧
  (!ts. MAP (infer_deBruijn_subst []) ts = ts)``,
  Induct>>rw[]>>fs[infer_deBruijn_subst_def,MAP_EQ_ID]);

val deBruijn_subst_nothing = store_thm("deBruijn_subst_nothing",
  ``(∀t.
  deBruijn_subst 0 [] t = t )∧
  ∀ts.
  MAP (deBruijn_subst 0 []) ts = ts``,
  ho_match_mp_tac astTheory.t_induction>>
  fs[deBruijn_subst_def]>>rw[]>>
  fs[LIST_EQ_REWRITE]>>rw[]>>
  fs[MEM_EL,EL_MAP]);

val infer_type_subst_nil = store_thm("infer_type_subst_nil",
  ``(∀t. check_freevars n [] t ⇒ infer_type_subst [] t = unconvert_t t) ∧
    (∀ts. EVERY (check_freevars n []) ts ⇒ MAP (infer_type_subst []) ts = MAP unconvert_t ts)``,
  ho_match_mp_tac(TypeBase.induction_of(``:t``)) >>
  rw[infer_type_subst_def,convert_t_def,unconvert_t_def,check_freevars_def] >>
  fsrw_tac[boolSimps.ETA_ss][]);

(* ---------- env_rel_e_sound, the invariant relating inference and type system * environments ---------- *)

(*Soundness invariant
Everything in the inferencer env is also in the type system env

1) If we are inside an expresesion, then their tvs is just 0 and the
   type system type is just the walk of the inferencer type

2) Else,
  the type system type scheme generalizes the inferencer's type scheme
*)

val tscheme_approx_def = Define `
  tscheme_approx max_tvs s (tvs,t) (tvs',t') ⇔
    !subst.
      LENGTH subst = tvs ∧
      EVERY (check_t max_tvs (FDOM s)) subst
      ⇒
      ?subst'.
        LENGTH subst' = tvs' ∧
        EVERY (check_t max_tvs (FDOM s)) subst' ∧
        t_walkstar s (infer_deBruijn_subst subst t) =
        t_walkstar s (infer_deBruijn_subst subst' t')`;

val env_rel_sound_def = Define `
  env_rel_sound s ienv tenv tenvE ⇔
    ienv.inf_t = tenv.t ∧
    ienv.inf_c = tenv.c ∧
    !x ts.
      nsLookup ienv.inf_v x = SOME ts
      ⇒
      ?tvs' t'.
        check_freevars (tvs' + num_tvs tenvE) [] t' ∧
        lookup_var x tenvE tenv = SOME (tvs', t') ∧
        tscheme_approx (num_tvs tenvE) s ts (tvs', unconvert_t t')`;

val env_rel_sound_lookup_some = Q.store_thm ("env_rel_sound_lookup_some",
  `!id ts s ienv tenv tenvE.
    nsLookup ienv.inf_v id = SOME ts ∧ env_rel_sound s ienv tenv tenvE
    ⇒
    ?tvs' t'.
      check_freevars (tvs' + num_tvs tenvE) [] t' ∧
      lookup_var id tenvE tenv = SOME (tvs',t') ∧
      tscheme_approx (num_tvs tenvE) s ts (tvs', unconvert_t t')`,
 rw [env_rel_sound_def]);

val db_subst_infer_subst_swap3 = Q.store_thm ("db_subst_infer_subst_swap3",
  `!t tvs s subst.
    t_wfs s ∧
    check_freevars tvs [] t
    ⇒
    convert_t (t_walkstar s (infer_deBruijn_subst subst (unconvert_t t)))
    =
    deBruijn_subst 0 (MAP (convert_t o t_walkstar s) subst) t`,
 ho_match_mp_tac unconvert_t_ind
 >> rw [unconvert_t_def, infer_deBruijn_subst_def, deBruijn_subst_def,
        check_freevars_def, convert_t_def, t_walkstar_eqn1]
 >- rw [EL_MAP]
 >> rw [MAP_MAP_o, combinTheory.o_DEF]
 >> rw [MAP_EQ_f]
 >> first_x_assum drule
 >> fs [EVERY_MEM]
 >> metis_tac []);

val tscheme_approx0 = Q.store_thm ("tscheme_approx0",
  `!tvs s t. t_wfs s ⇒ tscheme_approx tvs s (0, t) (0, t_walkstar s t)`,
 rw [tscheme_approx_def, LENGTH_NIL, infer_deBruijn_subst_id, t_walkstar_idempotent]);

val env_rel_sound_extend0 = Q.store_thm ("env_rel_sound_extend0",
  `!s x t ienv tenv tenvE.
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs s ∧
    check_t (num_tvs tenvE) (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    env_rel_sound s (ienv with inf_v := nsBind x (0,t) ienv.inf_v)
      tenv (Bind_name x 0 (convert_t (t_walkstar s t)) tenvE)`,
 rw [env_rel_sound_def]
 >> Cases_on `Short x = x'`
 >> rw []
 >> simp [lookup_var_def, lookup_varE_def, tveLookup_def, deBruijn_inc0]
 >- (
   `check_t (num_tvs tenvE) {} (t_walkstar s t)`
     by (
       irule (CONJUNCT1 check_t_walkstar)
       >> simp [])
   >> drule check_t_empty_unconvert_convert_id
   >> rw [check_t_to_check_freevars]
   >> fs []
   >> rw []
   >> metis_tac [tscheme_approx0])
 >- (
   fs []
   >> first_x_assum drule
   >> rw []
   >> every_case_tac
   >> fs [lookup_var_def, lookup_varE_def]));

val env_rel_sound_merge0 = Q.store_thm ("env_rel_sound_merge0",
  `!s ienv bindings tenv tenvE.
    t_wfs s ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv))) ∧
    EVERY (λ(x,t). check_t 0 (FDOM s) t) bindings ∧
    env_rel_sound s ienv tenv tenvE
    ⇒
    env_rel_sound s
       (ienv with inf_v := nsAppend (alist_to_ns (MAP (λ(n,t). (n,0,t)) bindings)) ienv.inf_v)
       tenv
       (bind_var_list 0 (convert_env s bindings) tenvE)`,
 rw [env_rel_sound_def]
 >> fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, nsLookup_alist_to_ns_none]
 >- (
   rw [lookup_var_def, lookup_varE_def, tveLookup_bvl, convert_env_def, deBruijn_inc0]
   >> fs [ALOOKUP_MAP]
   >> rw []
   >- (
     irule check_t_to_check_freevars
     >> irule (CONJUNCT1 check_t_walkstar)
     >> rw []
     >> fs [EVERY_MEM]
     >> imp_res_tac ALOOKUP_MEM
     >> first_x_assum drule
     >> fs []
     >> metis_tac [check_t_more2, DECIDE ``x + 0n = x``])
   >- (
     rw [tscheme_approx_def]
     >> qexists_tac `subst`
     >> fs [LENGTH_NIL]
     >> rw []
     >> simp [infer_deBruijn_subst_id]
     >> fs []
     >> `check_t (num_tvs tenvE) {} (t_walkstar s t)`
       by (
         irule (CONJUNCT1 check_t_walkstar)
         >> simp []
         >> imp_res_tac ALOOKUP_MEM
         >> fs [EVERY_MEM]
         >> first_x_assum drule
         >> rw []
         >> metis_tac [check_t_more2, DECIDE ``z + 0n = z``])
     >> drule check_t_empty_unconvert_convert_id
     >> rw []
     >> fs [t_walkstar_idempotent]))
 >- (
   first_x_assum drule
   >> rw [lookup_var_def, lookup_varE_def]
   >> CASE_TAC
   >> fs [tveLookup_bvl]
   >> every_case_tac
   >> fs [deBruijn_inc0, ALOOKUP_MAP, convert_env_def]
   >> fs []));

val env_rel_e_sound_letrec_merge0 = Q.store_thm ("env_rel_e_sound_letrec_merge0",
`!funs ienv tenv tenvE s uvs.
  t_wfs s ∧
  (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv))) ∧
  count (uvs + LENGTH funs) ⊆ FDOM s ∧
  env_rel_sound s ienv tenv tenvE
  ⇒
  env_rel_sound s
    (ienv with inf_v :=
      nsAppend
        (alist_to_ns
          (MAP2 (λ(f,x,e) uvar. (f,0,uvar))
            funs
            (MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH funs)))))
        ienv.inf_v)
    tenv
    (bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t))
                       funs
                       (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (uvs + n))))
                         (COUNT_LIST (LENGTH funs)))) tenvE)`,
  induct_on `funs` >>
  srw_tac[] [COUNT_LIST_def, bind_var_list_def] >>
  PairCases_on `h` >>
  srw_tac[] [bind_var_list_def] >>
  last_x_assum drule >>
  disch_then drule >>
  full_simp_tac (bool_ss) [DECIDE ``x+SUC y=SUC x + y``] >>
  disch_then drule >>
  disch_then drule >>
  rw [] >>
  drule env_rel_sound_extend0 >>
  simp [MAP_MAP_o, combinTheory.o_DEF] >>
  disch_then (qspecl_then [`h0`, `Infer_Tuvar uvs`] mp_tac) >>
  simp [check_t_def] >>
  fs [SUBSET_DEF] >>
  simp_tac (srw_ss()++ARITH_ss) [ADD1]
  >> rw []
  >> ONCE_REWRITE_TAC [DECIDE ``n + (x + 1) = x + (n + 1n)``]
  >> metis_tac []);

(*

val env_rel_e_sound_empty_to = Q.store_thm ("env_rel_e_sound_empty_to",
`!s ienv tenv tenvE.
  t_wfs s ∧ ienv_ok {} ienv ∧ env_rel_e_sound FEMPTY ienv tenv tenvE
  ⇒
  env_rel_e_sound s ienv tenv tenvE`,
 rw [env_rel_e_sound_def]
 >> first_x_assum drule
 >> rw []
 >> rename1 `lookup_var _ _ _ = SOME (tvs', t')`
 >> qexists_tac `tvs'`
 >> qexists_tac `t'`
 >> simp []
 >> every_case_tac
 >> fs [t_walkstar_FEMPTY]
 >> rw []
 >- metis_tac [t_walkstar_FEMPTY]
 >> fs [ienv_ok_def, ienv_val_ok_def]
 >> imp_res_tac nsLookup_nsAll
 >> fs []);

          *)
(*
val env_rel_e_sound_extend = Q.store_thm ("env_rel_e_sound_extend",
`!s x tvs t env t' tenv.
  t_wfs s ∧
  env_rel_e_sound s env tenv
  ⇒
  env_rel_e_sound s ((x,tvs,t)::env) (bind_tenv x tvs (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)) tenv)`,
rw [env_rel_e_sound_def] >>
every_case_tac >>
rw [] >>
rw [lookup_tenv_def, bind_tenv_def, deBruijn_inc0] >>
imp_res_tac inc_wfs>>
fs[t_walkstar_no_vars]
metis_tac []);
*)

(*
val env_rel_e_sound_extend_tvar_empty_subst = Q.store_thm ("env_rel_e_sound_extend_tvar_empty_subst",
`!env tvs tenv.
  check_env {} env ∧ env_rel_e_sound FEMPTY env tenv ⇒ env_rel_e_sound FEMPTY env (bind_tvar tvs tenv)`,
  induct_on `env` >>
  fs [env_rel_e_sound_def] >>
  rw [] >>
  PairCases_on `h` >>
  rw [bind_tvar_def, lookup_tenv_val_def] >>
  fs [t_walkstar_FEMPTY] >>
  res_tac >>
  imp_res_tac lookup_tenv_val_inc >>
  fs[]>>
  reverse (Cases_on`h0=x`)>>fs[]
  >-
    (IF_CASES_TAC>>fs[deBruijn_inc0,num_tvs_def]
    >-
      (fs[nil_deBruijn_inc]>>
      metis_tac[])
    >>
    (fs[check_env_def,deBruijn_inc_def,EVERY_MEM]>>
    `MEM (x,0,t) env` by metis_tac[ALOOKUP_MEM]>>
    res_tac>>fs[]>>
    metis_tac[]))
  >>
    fs[check_env_def]>>rfs[nil_deBruijn_inc,num_tvs_def]>>
    metis_tac[])

val env_rel_e_sound_merge = Q.store_thm ("env_rel_e_sound_merge",
`!s x uv env env' tenv.
  t_wfs s ∧
  env_rel_e_sound s env tenv
  ⇒
  env_rel_e_sound s (MAP (λ(n,t). (n,0,t)) env' ++ env) (bind_var_list 0 (convert_env s env') tenv)`,
  induct_on `env'` >>
  rw [convert_env_def, bind_var_list_def] >>
  res_tac >>
  fs [env_rel_e_sound_def] >>
  rw [] >>
  PairCases_on `h` >>
  fs [] >>
  cases_on `h0 = x` >>
  fs [] >>
  rw [bind_var_list_def, lookup_tenv_val_def,
      deBruijn_inc0, infer_deBruijn_inc0_id, o_f_id]
  >-
    metis_tac[t_walkstar_no_vars,check_t_to_check_freevars]
  >-
    (qexists_tac`[]`>>fs[deBruijn_subst_def]>>
    imp_res_tac check_t_to_check_freevars>>
    imp_res_tac deBruijn_subst_id>>
    fs[COUNT_LIST_def]>>
    metis_tac[t_walkstar_no_vars])
  >>
    res_tac>>
    fs[convert_env_def,num_tvs_def])
    *)

(*
val env_rel_e_sound_merge2 = Q.store_thm ("env_rel_e_sound_merge2",
`!env tenv env'' s tvs.
  env_rel_e_sound FEMPTY env tenv
  ⇒
  env_rel_e_sound FEMPTY
    (MAP (λx. (FST x,tvs,t_walkstar s (SND x))) env'' ++ env)
    (bind_var_list2 (MAP (λx. (FST x,tvs, convert_t (t_walkstar s (SND x)))) env'') tenv)`,
induct_on `env''` >>
rw [bind_var_list2_def] >>
PairCases_on `h` >>
rw [bind_var_list2_def] >>
res_tac >>
fs [env_rel_e_sound_def, bind_tenv_def, lookup_tenv_def] >>
rw [deBruijn_inc0, t_walkstar_FEMPTY] >>
metis_tac [t_walkstar_FEMPTY]);

val env_rel_e_sound_merge3 = Q.store_thm ("env_rel_e_sound_merge3",
`!l l' env tenv s tvs.
(LENGTH l = LENGTH l') ∧
env_rel_e_sound FEMPTY env tenv
⇒
env_rel_e_sound FEMPTY
     (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
        (MAP (λx. t_walkstar s (Infer_Tuvar x))
           l') ++ env)
  (bind_var_list2
     (MAP (λ(x,tvs,t). (x,tvs,convert_t t))
        (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
           (MAP (λx. t_walkstar s (Infer_Tuvar x))
              l'))) tenv)`,
induct_on `l` >>
rw [] >>
cases_on `l'` >>
rw [bind_var_list2_def] >>
fs [] >>
PairCases_on `h` >>
fs [bind_var_list2_def] >>
fs [env_rel_e_sound_def, bind_tenv_def, lookup_tenv_def] >>
rw [deBruijn_inc0, t_walkstar_FEMPTY] >>
fs [t_walkstar_FEMPTY] >>
res_tac >>
metis_tac []);
*)


(*
val env_rel_e_sound_convert_env2 = Q.store_thm ("env_rel_e_sound_convert_env2",
`∀env. check_env {} env ⇒
 env_rel_e_sound FEMPTY env (bind_var_list2 (convert_env2 env) Empty)`,
  Induct >>
  rw [convert_env2_def, bind_var_list2_def, env_rel_e_sound_def] >>
  PairCases_on `h` >>
  Cases_on`h0=x`>>fs[lookup_tenv_val_def,bind_var_list2_def,check_env_def]>>
  fs[deBruijn_inc0]
  >-
    (fs[check_t_to_check_freevars]>>
    qexists_tac`MAP (Tvar_db) (COUNT_LIST tvs)` >>
    fs[LENGTH_COUNT_LIST]>>
    CONJ_TAC
    >-
      fs[EVERY_MAP,COUNT_LIST_GENLIST,EVERY_GENLIST,check_freevars_def]
    >>
    match_mp_tac (deBruijn_subst_id |> CONJUNCT1)>>
    fs[check_t_to_check_freevars])
  >>
  fs[env_rel_e_sound_def]>>
  res_tac>>
  Cases_on`check_t tvs {} t` >> fs[convert_env2_def])
  *)

(*
val tenv_invC_def = Define `
  tenv_invC s tenv tenvE =
  (∀x tvs t.
    lookup_tenv_val x 0 tenvE = SOME (tvs, t)
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
    *)

val infer_deBruijn_subst_id2 = store_thm("infer_deBruijn_subst_id2",
  ``(∀t.
  check_t tvs {} t ⇒
  infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs) t = t) ∧
  (∀ts.
  EVERY (check_t tvs {}) ts ⇒
  MAP (infer_deBruijn_subst (GENLIST (Infer_Tvar_db) tvs)) ts = ts)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]>>fs[check_t_def]
  >-
    fs[infer_deBruijn_subst_def]
  >>
    fs[infer_deBruijn_subst_def,EVERY_MEM]>>
    metis_tac[]);

    (*
val tenv_invC_convert_env2 = Q.store_thm ("tenv_invC_convert_env2",
`!env. check_env {} env ⇒ tenv_invC FEMPTY env (bind_var_list2 (convert_env2 env) Empty)`,
  Induct >>
  rw [convert_env2_def, bind_var_list2_def, tenv_invC_def] >>
  fs[lookup_tenv_val_def]>>
  PairCases_on `h` >>
  Cases_on`h0=x`>>fs[lookup_tenv_val_def,bind_var_list2_def,check_env_def]>>
  fs[deBruijn_inc0]
  >-
    metis_tac[check_t_to_check_freevars]
  >-
    (fs[tenv_invC_def,convert_env2_def]>>
    metis_tac[])
  >-
    (fs[check_t_to_check_freevars]>>
    qexists_tac`GENLIST Infer_Tvar_db tvs` >>
    fs[LENGTH_COUNT_LIST]>>
    CONJ_TAC
    >-
      fs[EVERY_MAP,COUNT_LIST_GENLIST,EVERY_GENLIST,check_t_def]
    >>
    qpat_x_assum `A=t` (SUBST_ALL_TAC o SYM)>>
    imp_res_tac check_t_empty_unconvert_convert_id>>
    fs[]>>
    match_mp_tac (infer_deBruijn_subst_id2 |> CONJUNCT1)>>
    fs[check_t_to_check_freevars])
  >>
  fs[tenv_invC_def,convert_env2_def])

  *)

  (*
val menv_alpha_def = Define`
  menv_alpha = fmap_rel (λitenv tenv. tenv_alpha itenv (bind_var_list2 tenv Empty))`
  *)

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
  fsrw_tac[][check_t_def]
  >-
    (fsrw_tac[][generalise_def]>>
    qpat_x_assum`A=(a,b,t')` mp_tac>>BasicProvers.LET_ELIM_TAC>>
    fsrw_tac[][]>>
    first_assum match_mp_tac>>
    ntac 2 HINT_EXISTS_TAC >>
    fsrw_tac[][EVERY_MEM,t_vars_eqn,SUBSET_DEF,MEM_MAP]>>
    metis_tac[])
  >-
    (imp_res_tac generalise_subst>>
    fsrw_tac[][generalise_def]>>
    full_case_tac>>fsrw_tac[][]
    >-
      (qexists_tac`[t_walkstar s (Infer_Tuvar n)]`>>
      qpat_x_assum`A=b` sym_sub_tac>>
      srw_tac[][]
      >-
        (simp[FAPPLY_FUPDATE_THM]>>
        `x ≠ n` by
          (CCONTR_TAC>>
          fs[flookup_thm])>>
        fs[]>>
        `smap ' x < LENGTH subst` by fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>
        simp[EL_APPEND1])
      >>
      fs[t_vars_eqn,EL_LENGTH_APPEND])
    >>
    qexists_tac`[]`>>fs[EXTENSION]>>
    metis_tac[])
  >-
    (fs[generalise_def]>>
    qexists_tac`[]`>>fs[])
  >>
    fsrw_tac[][generalise_def]>>
    qpat_x_assum`A=(a,b,t')` mp_tac>>BasicProvers.LET_ELIM_TAC>>
    imp_res_tac generalise_subst>>
    first_x_assum(qspecl_then[`subst`,`smap`,`num_gen`,`s'`,`t'`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then[`subst++subst'`,`s'`,`num_gen'`,`s''`,`ts''`] mp_tac)>>
    impl_tac>-
      (fsrw_tac [ARITH_ss] []>>
      reverse CONJ_TAC>-
        metis_tac[]>>
      fs[IN_FRANGE,SUBSET_DEF,PULL_EXISTS]>>
      gen_tac>>Cases_on`k ∈ FDOM smap`>>fs[]>>
      fs[SUBMAP_DEF]>>
      res_tac>>
      DECIDE_TAC)>>
    rw[]>>
    qexists_tac`subst'++subst''`>>fs[]>>
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
  ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
  fs[infer_subst_def,t_walkstar_eqn1,check_t_def,infer_deBruijn_subst_def]
  >-
    (fs[LIST_EQ_REWRITE,EL_MAP,t_vars_eqn,PULL_EXISTS,SUBSET_DEF,MEM_MAP]>>
    rw[]>>
    first_assum (match_mp_tac o MP_CANON)>>
    fs[EVERY_MEM]>>
    metis_tac[])
  >>
  (fs[t_vars_eqn] >> imp_res_tac flookup_thm>>
  fs[PULL_FORALL]>>
  fs[infer_deBruijn_subst_def]>>
  reverse IF_CASES_TAC
  >- (fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>metis_tac[])
  >> REFL_TAC))

  (*
val tenv_alpha_empty = store_thm("tenv_alpha_empty",``
  tenv_alpha [] (bind_var_list2 [] Empty)``,
  fs[tenv_alpha_def,bind_var_list2_def,env_rel_e_sound_def,tenv_invC_def,lookup_tenv_val_def])

val tenv_alpha_convert = store_thm("tenv_alpha_convert",
  ``check_env ∅ tenv ⇒
    tenv_alpha tenv (bind_var_list2 (convert_env2 tenv) Empty) ``,
  rw[tenv_alpha_def,env_rel_e_sound_convert_env2,tenv_invC_convert_env2])

val menv_alpha_convert = store_thm("menv_alpha_convert",
  ``check_menv menv ⇒ menv_alpha menv (convert_menv menv)``,
  rw[menv_alpha_def,convert_menv_def,fmap_rel_OPTREL_FLOOKUP,optionTheory.OPTREL_def,FLOOKUP_o_f] >>
  CASE_TAC >>
  fs[check_menv_def,FEVERY_ALL_FLOOKUP] >>
  res_tac >> fs[GSYM check_env_def] >>
  rw[GSYM convert_env2_def, tenv_alpha_convert])

val env_rel_e_sound_bind_var_list2 = prove(``
  env_rel_e_sound FEMPTY itenv (bind_var_list2 tenv Empty) ∧
  env_rel_e_sound FEMPTY itenv' (bind_var_list2 tenv' Empty) ∧
  set (MAP FST itenv) = set (MAP FST tenv)
  ⇒
  env_rel_e_sound FEMPTY (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  rw[env_rel_e_sound_def]>>
  fs[GSYM bvl2_lookup]>>
  fs[ALOOKUP_APPEND]>>
  Cases_on`ALOOKUP itenv x`>>fs[]
  >-
    (`ALOOKUP tenv x = NONE` by metis_tac[ALOOKUP_NONE,EXTENSION]>>
    fs[])
  >>
    qpat_x_assum`x'=A` SUBST_ALL_TAC>>
    res_tac>>
    fs[])

val tenv_invC_bind_var_list2 = prove(``
  tenv_invC FEMPTY itenv (bind_var_list2 tenv Empty) ∧
  tenv_invC FEMPTY itenv' (bind_var_list2 tenv' Empty) ∧
  set (MAP FST itenv) = set (MAP FST tenv)
  ⇒
  tenv_invC FEMPTY (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  rw[tenv_invC_def]>>
  fs[GSYM bvl2_lookup]>>
  fs[ALOOKUP_APPEND]>>
  Cases_on `ALOOKUP tenv x`>>fs[]
  >-
    metis_tac[]
  >-
    metis_tac[]
  >-
    (`ALOOKUP itenv x = NONE` by metis_tac[ALOOKUP_NONE,EXTENSION]>>
    fs[])
  >>
    qpat_x_assum`x'=A` SUBST_ALL_TAC>>
    res_tac>>
    fs[])

val tenv_alpha_bind_var_list2 = store_thm("tenv_alpha_bind_var_list2",``
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧
  set (MAP FST itenv) = set (MAP FST tenv) ∧
  tenv_alpha itenv' (bind_var_list2 tenv' Empty)
  ⇒
  tenv_alpha (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,
  fs[tenv_alpha_def]>>
  metis_tac[env_rel_e_sound_bind_var_list2,env_rel_e_soundC_bind_var_list2])

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
  conj_tac >- rw[check_weakE_def,success_eqns] >>
  rw[check_weakE_def] >>
  Cases_on`ALOOKUP env_impl n`>>simp[failwith_def] >>
  Cases_on`x`>>simp[success_eqns,init_state_def] >> fs[] >>
  simp[markerTheory.Abbrev_def] >>
  simp[init_infer_state_def] >>
  simp[COUNT_LIST_GENLIST,MAP_GENLIST,ETA_AX] >>
  simp[IS_SOME_EXISTS,PULL_EXISTS] >>
  rw[EQ_IMP_THM] >> rw[] >- (
    fs[LET_THM,IS_SOME_EXISTS] >>
    metis_tac[] ) >>
  simp[markerTheory.Abbrev_def,IS_SOME_EXISTS] )

val convert_env2_anub = store_thm("convert_env2_anub",
  ``∀ls ac. convert_env2 (anub ls ac) = anub (convert_env2 ls) ac``,
  Induct >> fs[anub_def,convert_env2_def] >>
  fs[UNCURRY] >>
  Cases >> fs[anub_def,UNCURRY] >> rw[] >>
  Cases_on`r`>>fs[])

val tenv_bvl_def = Define`
  tenv_bvl venv ⇔  ∃tenv_v. venv = bind_var_list2 tenv_v Empty`

(*Environment relation at infer_d and above*)
val env_rel_def = Define`
 env_rel tenv ienv ⇔
  tenv_bvl tenv.v ∧
  tenv_val_ok tenv.v ∧
  tenv_mod_ok tenv.m ∧
  check_menv ienv.inf_m ∧
  menv_alpha ienv.inf_m tenv.m ∧
  check_cenv tenv.c ∧
  ienv.inf_c = tenv.c ∧
  tenv_tabbrev_ok tenv.t ∧
  ienv.inf_t = tenv.t ∧
  check_env ∅ ienv.inf_v ∧
  tenv_alpha ienv.inf_v tenv.v`
  *)

val _ = export_theory ();
