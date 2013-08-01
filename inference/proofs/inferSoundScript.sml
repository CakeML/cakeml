open preamble;
open rich_listTheory;
open LibTheory TypeSystemTheory AstTheory SemanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open typeSysPropsTheory;

(* Remove automatic rewrites that break the proofs in this file *)
val _ = diminish_srw_ss ["semanticsExtra"];

val fupdate_list_map = Q.prove (
`!l f x y.
  x ∈ FDOM (FEMPTY |++ l)
   ⇒
     ((FEMPTY |++ MAP (\(a,b). (a, f b)) l) ' x = f ((FEMPTY |++ l) ' x))`,
     rpt gen_tac >>
     Q.ISPECL_THEN[`FST`,`f o SND`,`l`,`FEMPTY:α|->γ`]mp_tac(GSYM miscTheory.FOLDL_FUPDATE_LIST) >>
     simp[LAMBDA_PROD] >>
     disch_then kall_tac >>
     qid_spec_tac`l` >>
     ho_match_mp_tac SNOC_INDUCT >>
     simp[FUPDATE_LIST_THM] >>
     simp[FOLDL_SNOC,FORALL_PROD,FAPPLY_FUPDATE_THM,FDOM_FUPDATE_LIST,MAP_SNOC,miscTheory.FUPDATE_LIST_SNOC] >>
     rw[] >> rw[])

val fdom_fupdate_list2 = Q.prove (
`∀kvl fm. FDOM (fm |++ kvl) = (FDOM fm DIFF set (MAP FST kvl)) ∪ set (MAP FST kvl)`,
rw [FDOM_FUPDATE_LIST, EXTENSION] >>
metis_tac []);

val map_fst = Q.prove (
`!l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l`,
induct_on `l` >>
rw [] >>
PairCases_on `h` >>
fs []);

val lookup_all_distinct = Q.prove (
`!l x y.
  ALL_DISTINCT (MAP FST l) ∧
  MEM (x,y) l
  ⇒
  (lookup x l = SOME y)`,
Induct_on `l` >>
rw [lookup_def] >>
rw [lookup_def] >>
PairCases_on `h` >>
rw [] >>
fs [MEM_MAP] >>
metis_tac [FST]);

val flookup_update_list_none = Q.prove (
`!x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (lookup x l = NONE))`,
induct_on `l` >>
rw [FUPDATE_LIST_THM] >>
PairCases_on `h` >>
rw [FLOOKUP_DEF]);

val flookup_update_list_some = Q.prove (
`!x m l y. 
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((lookup x (REVERSE l) = SOME y) ∨
   ((lookup x l = NONE) ∧ (FLOOKUP m x = SOME y)))`,
Induct_on `l` >>
rw [FUPDATE_LIST_THM] >>
PairCases_on `h` >>
rw [lookup_append, FLOOKUP_UPDATE] >|
[cases_on `lookup h0 (REVERSE l)` >>
     rw [] >>
     metis_tac [lookup_reverse_none, optionTheory.NOT_SOME_NONE],
 cases_on `lookup x (REVERSE l)` >>
     rw []]);

val every_count_list = Q.prove (
`!P n. EVERY P (COUNT_LIST n) = (!m. m < n ⇒ P m)`,
induct_on `n` >>
rw [COUNT_LIST_def, EVERY_MAP] >>
eq_tac >>
rw [] >>
cases_on `m` >>
rw [] >>
`n' < n` by decide_tac >>
metis_tac []);

val filter_helper = Q.prove (
`!x l1 l2. ~MEM x l2 ⇒ MEM x (FILTER (\x. x ∉ set l2) l1) = MEM x l1`,
induct_on `l1` >>
rw [] >>
metis_tac []);

val nub_append = Q.prove (
`!l1 l2.
  nub (l1++l2) = nub (FILTER (\x. ~MEM x l2) l1) ++ nub l2`,
induct_on `l1` >>
rw [nub_def] >>
fs [] >>
full_case_tac >>
rw [] >>
metis_tac [filter_helper]);

val list_to_set_diff = Q.prove (
`!l1 l2. set l2 DIFF set l1 = set (FILTER (\x. x ∉ set l1) l2)`,
induct_on `l2` >>
rw []);

val card_eqn_help = Q.prove (
`!l1 l2. CARD (set l2) - CARD (set l1 ∩ set l2) = CARD (set (FILTER (\x. x ∉ set l1) l2))`,
rw [Once INTER_COMM] >>
SIMP_TAC list_ss [GSYM CARD_DIFF] >>
metis_tac [list_to_set_diff]);

val length_nub_append = Q.prove (
`!l1 l2. LENGTH (nub (l1 ++ l2)) = LENGTH (nub l1) + LENGTH (nub (FILTER (\x. ~MEM x l1) l2))`,
rw [GSYM ALL_DISTINCT_CARD_LIST_TO_SET, all_distinct_nub, GSYM nub_set] >>
fs [FINITE_LIST_TO_SET, CARD_UNION_EQN] >>
ASSUME_TAC (Q.SPECL [`l1`, `l2`] card_eqn_help) >>
`CARD (set l1 ∩ set l2) ≤ CARD (set l2)` 
           by metis_tac [CARD_INTER_LESS_EQ, FINITE_LIST_TO_SET, INTER_COMM] >>
decide_tac);

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
rw [fmap_EXT]);

val lookup_tenv_inc = Q.prove (
`!x inc tenv tvs t inc2.
  (lookup_tenv x inc tenv = SOME (tvs,t))
  ⇒
  (lookup_tenv x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t))`,
induct_on `tenv` >>
rw [lookup_tenv_def] >>
rw [deBruijn_inc_deBruijn_inc] >>
metis_tac [arithmeticTheory.ADD_ASSOC]);

val every_zip_snd = Q.prove (
`!l1 l2 P.
(LENGTH l1 = LENGTH l2) ⇒
(EVERY (\x. P (SND x)) (ZIP (l1,l2)) = EVERY P l2)`,
induct_on `l1` >>
rw [] >>
cases_on `l2` >>
fs []);

val every_zip_fst = Q.prove (
`!l1 l2 P.
(LENGTH l1 = LENGTH l2) ⇒
(EVERY (\x. P (FST x)) (ZIP (l1,l2)) = EVERY P l1)`,
induct_on `l1` >>
rw [] >>
cases_on `l2` >>
fs []);

val every_shim = Q.prove (
`!l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)`,
induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw []);

val every_shim2 = Q.prove (
`!l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)`,
induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw [] >>
metis_tac []);

(*
val deBruijn_inc_inc = Q.prove (
`(!t inc1 inc2.
  deBruijn_inc inc2 inc1 (deBruijn_inc 0 inc2 t) = deBruijn_inc 0 (inc1 + inc2) t) ∧
 (!ts inc1 inc2.
  MAP (deBruijn_inc inc2 inc1 o deBruijn_inc 0 inc2) ts = MAP (deBruijn_inc 0 (inc1 + inc2)) ts)`,
Induct >>
rw [deBruijn_inc_def, MAP_MAP_o] >-
decide_tac >-
decide_tac >>
metis_tac []);
*)

val fmap_to_list = Q.prove (
`!m. ?l. ALL_DISTINCT (MAP FST l) ∧ (m = FEMPTY |++ l)`,
ho_match_mp_tac fmap_INDUCT >>
rw [FUPDATE_LIST_THM] >|
[qexists_tac `[]` >>
     rw [FUPDATE_LIST_THM],
 qexists_tac `(x,y)::l` >>
     rw [FUPDATE_LIST_THM] >>
     fs [FDOM_FUPDATE_LIST] >>
     rw [FUPDATE_FUPDATE_LIST_COMMUTES] >>
     fs [LIST_TO_SET_MAP] >>
     metis_tac [FST]]);

val _ = new_theory "inferSound";

val infer_deBruijn_inc_def = tDefine "infer_deBruijn_inc" `
(infer_deBruijn_inc n (Infer_Tvar_db m) = 
  Infer_Tvar_db (m + n)) ∧
(infer_deBruijn_inc n (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) ∧
(infer_deBruijn_inc n (Infer_Tuvar m) = 
  Infer_Tuvar m)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val infer_deBruijn_inc_inc = Q.prove (
`(!t inc1 inc2.
  (infer_deBruijn_inc inc1 o infer_deBruijn_inc inc2) t = infer_deBruijn_inc (inc1 + inc2) t) ∧
 (!ts inc1 inc2.
  MAP (infer_deBruijn_inc inc1 o infer_deBruijn_inc inc2) ts = MAP (infer_deBruijn_inc (inc1 + inc2)) ts)`,
Induct >>
rw [infer_deBruijn_inc_def, MAP_MAP_o] >-
decide_tac >>
metis_tac []);

val t_unify_apply = Q.prove (
`!s1 s2 t1 t2.
  t_wfs s1 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
metis_tac [t_unify_unifier]);

val t_unify_apply2 = Q.prove (
`!s1 s2 t1' t2' t1 t2.
  t_wfs s1 ∧
  (t_unify s1 t1' t2' = SOME s2) ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
rw [] >>
`t_wfs s2 ∧ s1 SUBMAP s2` by metis_tac [t_unify_unifier] >>
metis_tac [t_walkstar_SUBMAP]);

val t_unify_wfs = Q.store_thm ("t_unify_wfs",
`!s1 t1 t2 s2.
  t_wfs s1 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  t_wfs s2`,
metis_tac [t_unify_unifier]);

val t_vars_inc = Q.prove (
`!tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [t_vars_def, encode_infer_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw [encode_infer_t_def]);

val inc_wfs = Q.prove (
`!tvs s. t_wfs s ⇒ t_wfs (infer_deBruijn_inc tvs o_f s)`,
rw [t_wfs_eqn] >>
`t_vR s = t_vR (infer_deBruijn_inc tvs o_f s)`
       by (rw [FLOOKUP_o_f, FUN_EQ_THM, t_vR_eqn] >>
           full_case_tac  >>
           rw [t_vars_inc]) >>
metis_tac []);

val vwalk_inc = Q.prove (
`!s tvs n.
  t_wfs s
  ⇒
  t_vwalk (infer_deBruijn_inc tvs o_f s) n = infer_deBruijn_inc tvs (t_vwalk s n)`,
rw [] >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
rw [] >>
Q.SPEC_TAC (`n`, `n`) >>
qpat_assum `!p. (!v. q v ⇒ p v) ⇒ !v. p v` ho_match_mp_tac >>
rw [] >>
imp_res_tac t_vwalk_eqn >>
once_asm_rewrite_tac [] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
cases_on `FLOOKUP s n` >>
rw [FLOOKUP_o_f, infer_deBruijn_inc_def] >>
cases_on `x` >>
rw [infer_deBruijn_inc_def]);

val walk_inc = Q.prove (
`!s tvs t.
  t_wfs s
  ⇒
  t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) = infer_deBruijn_inc tvs (t_walk s t)`,
rw [] >>
cases_on `t` >>
rw [t_walk_eqn, infer_deBruijn_inc_def, vwalk_inc]);

val walkstar_inc = Q.prove (
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

val finite_t_rangevars = Q.prove (
`!t. FINITE (t_rangevars t)`,
rw [t_rangevars_eqn, t_vars_def] >>
rw [termTheory.FINITE_vars]);

val walkstar_inc2 = Q.prove (
`!tvs s n.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
   infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))`,
rw [GSYM walkstar_inc, infer_deBruijn_inc_def]);

val flookup_thm = Q.prove (
`!f x v. ((FLOOKUP f x = NONE) = (x ∉ FDOM f)) ∧
         ((FLOOKUP f x = SOME v) = (x ∈ FDOM f ∧ (f ' x = v)))`,
rw [FLOOKUP_DEF]);

val lookup_map = Q.prove (
`!n env v f. 
  (lookup n env = SOME v) ⇒ (lookup n (MAP (\(x,y). (x, f y)) env) = SOME (f v))`,
ho_match_mp_tac lookup_ind >>
rw []);

val count_add1 = Q.prove (
`!n. count (n + 1) = n INSERT count n`,
metis_tac [COUNT_SUC, arithmeticTheory.ADD1]);

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

val infer_st_rewrs = Q.prove (
`(!st. (st with next_uvar := st.next_uvar) = st) ∧
 (!st. (st with subst := st.subst) = st) ∧
 (!st s. (st with subst := s).subst = s) ∧
 (!st s. (st with subst := s).next_uvar = st.next_uvar) ∧
 (!st uv. (st with next_uvar := uv).next_uvar = uv) ∧
 (!st uv. (st with next_uvar := uv).subst = st.subst)`,
rw [] >>
cases_on `st` >>
rw [infer_st_component_equality]);

val count_list_sub1 = Q.prove (
`!n. (n ≠ 0) ⇒ (COUNT_LIST n = 0::MAP SUC (COUNT_LIST (n - 1)))`,
induct_on `n` >>
ONCE_REWRITE_TAC [COUNT_LIST_def] >>
fs []);

val el_map_count = Q.prove (
`!n f m. n < m ⇒ EL n (MAP f (COUNT_LIST m)) = f n`,
induct_on `n` >>
rw [] >>
cases_on `m` >>
fs [COUNT_LIST_def] >>
`n < SUC n'` by decide_tac >>
res_tac >>
fs [COUNT_LIST_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (mp_tac o GSYM o Q.SPEC `f o SUC`) >>
rw [MAP_MAP_o]);

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

val pure_add_constraints_def = Define `
(pure_add_constraints s [] s' = (s = s')) ∧
(pure_add_constraints s1 ((t1,t2)::rest) s' = 
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s')`;

val pure_add_constraints_ind = fetch "-" "pure_add_constraints_ind";

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

val pure_add_constraints_apply = Q.prove (
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

val pure_add_constraints_append = Q.prove (
`!s1 ts1 s3 ts2. 
  pure_add_constraints s1 (ts1 ++ ts2) s3
  =
  (?s2. pure_add_constraints s1 ts1 s2 ∧ pure_add_constraints s2 ts2 s3)`,
ho_match_mp_tac pure_add_constraints_ind >>
rw [pure_add_constraints_def] >>
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
`!pr x l st v st'. 
  (lookup_st_ex pr x l st = (Success v, st'))
  =
  ((lookup x l = SOME v) ∧ (st = st'))`,
ho_match_mp_tac lookup_st_ex_ind >>
rw [lookup_st_ex_def, lookup_def, failwith_def, st_ex_return_success]);

val constrain_uop_success = Q.prove (
`!uop t st v st'.
  (constrain_uop uop t st = (Success v, st'))
  =
  (((uop = Opref) ∧ (st = st') ∧ (v = Infer_Tapp [t] TC_ref)) ∨
   ((uop = Opderef) ∧ 
    (?uvar st''. ((fresh_uvar : ((num |-> infer_t) infer_st, infer_t, string) M) st = (Success uvar, st'')) ∧
                 (v = uvar) ∧
                 (add_constraint t (Infer_Tapp [uvar] TC_ref) st'' = (Success (), st')))))`,
rw [constrain_uop_def] >>
full_case_tac >>
rw [st_ex_return_success, st_ex_bind_success, oneTheory.one] >>
metis_tac []);

val op_case_expand = Q.prove (
`!f1 f2 f3 f4 f5 op st v st'.
  ((case op of
       Opn opn => f1
     | Opb opb => f2
     | Equality => f3
     | Opapp => f4
     | Opassign => f5) st
   = (Success v, st'))
  =
  ((?opn. (op = Opn opn) ∧ (f1 st = (Success v, st'))) ∨
   (?opb. (op = Opb opb) ∧ (f2 st = (Success v, st'))) ∨
   ((op = Equality) ∧ (f3 st = (Success v, st'))) ∨
   ((op = Opapp) ∧ (f4 st = (Success v, st'))) ∨
   ((op = Opassign) ∧ (f5 st = (Success v, st'))))`,
rw [] >>
cases_on `op` >>
rw []);

val constrain_op_success = 
  SIMP_CONV (srw_ss()) [constrain_op_def, op_case_expand, st_ex_bind_success,
                        st_ex_return_success, add_constraint_success]
  ``(constrain_op op t1 t2 st = (Success v, st'))``

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
             constrain_uop_success, constrain_op_success, oneTheory.one,
             get_next_uvar_success, apply_subst_list_success, guard_success,
             read_def, option_case_eq];

val _ = save_thm ("success_eqns", success_eqns);

val check_t_def = tDefine "check_t" `
(check_t n uvars (Infer_Tuvar v) = (v ∈ uvars)) ∧
(check_t n uvars (Infer_Tvar_db n') = 
  (n' < n)) ∧
(check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars) ts)`
(WF_REL_TAC `measure (infer_t_size o SND o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val check_env_def = Define `
check_env uvars env =
  EVERY (\(x, (tvs,t)). check_t tvs uvars t) env`;

val check_menv_def = Define `
check_menv menv =
  EVERY (\(mn,env). EVERY (\(x, (tvs,t)). check_t tvs {} t) env) menv`;

val check_cenv_def = Define `
check_cenv (cenv : tenvC) = 
  EVERY (\(cn,(tvs,ts,t)). EVERY (check_freevars 0 tvs) ts) cenv`;

val check_s_def = Define `
check_s tvs uvs s = 
  !uv. uv ∈ FDOM s ⇒ check_t tvs uvs (s ' uv)`;

val convert_t_def = tDefine "convert_t" `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`
(WF_REL_TAC `measure infer_t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val convert_menv_def = Define `
convert_menv menv = 
  MAP (\(mn,env). (mn, MAP (\(x,(tvs,t)). (x,(tvs,convert_t t))) env)) menv`;

val remove_pair_lem = Q.prove (
`(!f v. (\(x,y). f x y) v = f (FST v) (SND v)) ∧
 (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND (SND v)))`,
rw [] >>
PairCases_on `v` >>
rw []);

val check_convert_freevars = Q.prove (
`(!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_freevars_def, check_t_def, convert_t_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []);

val check_t_more = Q.prove (
`(!t tvs. check_t tvs {} t ⇒ !uvs. check_t tvs uvs t) ∧
 (!ts tvs. EVERY (check_t tvs {}) ts ⇒ !uvs. EVERY (check_t tvs uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []);

val check_t_more2 = Q.prove (
`(!t tvs uvs. check_t tvs uvs t ⇒ !tvs'. check_t (tvs' + tvs) uvs t) ∧
 (!ts tvs uvs. EVERY (check_t tvs uvs) ts ⇒ !tvs'. EVERY (check_t (tvs' + tvs) uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
decide_tac >>
metis_tac []);

val check_t_more3 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. check_t tvs (count (uvs + uvs')) t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. EVERY (check_t tvs (count (uvs + uvs'))) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
metis_tac [] >>
decide_tac);

val check_t_more4 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. uvs ≤ uvs' ⇒ check_t tvs (count uvs') t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. uvs ≤ uvs' ⇒ EVERY (check_t tvs (count uvs')) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac [ARITH_ss] [check_t_def] >>
metis_tac []);

val check_t_more5 = Q.prove (
`(!t uvs tvs. check_t tvs uvs t ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_t tvs uvs' t) ∧
 (!ts uvs tvs. EVERY (check_t tvs uvs) ts ⇒ !uvs'. uvs ⊆ uvs' ⇒ EVERY (check_t tvs uvs') ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, SUBSET_DEF] >>
metis_tac []);

val check_t_t_vars = Q.prove (
`!tvs uvs t.
  check_t tvs uvs t ⇒ t_vars t ⊆ uvs`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [t_vars_eqn, check_t_def, EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
metis_tac []);

val check_s_more = Q.prove (
`!s tvs uvs. check_s tvs (count uvs) s ⇒ check_s tvs (count (uvs + 1)) s`,
rw [check_s_def] >>
metis_tac [check_t_more3]);

val check_s_more2 = Q.prove (
`!s uvs. check_s tvs (count uvs) s ⇒ !uvs'. uvs ≤ uvs' ⇒ check_s tvs (count uvs') s`,
rw [check_s_def] >>
metis_tac [check_t_more4]);

val infer_p_next_uvar_mono = Q.prove (
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

val infer_e_next_uvar_mono = Q.prove (
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
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [infer_p_next_uvar_mono, arithmeticTheory.LESS_EQ_TRANS,
           pair_CASES,
           DECIDE ``!(x:num) y. x ≤ x + y``,
           DECIDE ``!(x:num) y. x + 1 ≤ y ⇒ x ≤ y``,
           DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``]);

val infer_p_constraints = Q.prove (
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

val infer_e_constraints = Q.prove (
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
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
TRY (cases_on `v'`) >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, infer_p_constraints]);

val pure_add_constraints_wfs = Q.store_thm ("pure_add_constraints_wfs",
`!s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  t_wfs s2`,
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

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
fs [] >>
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
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
fs [] >>
res_tac >>
imp_res_tac t_unify_wfs >>
fs [] >>
imp_res_tac pure_add_constraints_wfs >>
fs [] >>
cases_on `v'` >>
imp_res_tac infer_p_wfs >>
fs []);

val sub_completion_def = Define `
sub_completion tvs next_uvar s1 extra_constraints s2 =
  (pure_add_constraints s1 extra_constraints s2 ∧
   (count next_uvar SUBSET FDOM s2) ∧
   (!uv. uv ∈ FDOM s2 ⇒ check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv))))`;

val sub_completion_unify = Q.prove (
`!st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n (st.next_uvar + 1) s1 ts s2
  ⇒
  sub_completion n st.next_uvar st.subst ((t1,t2)::ts) s2`,
rw [sub_completion_def, pure_add_constraints_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]);

val sub_completion_unify2 = Q.prove (
`!st t1 t2 s1 n ts s2 n s3 next_uvar.
  (t_unify s1 t1 t2 = SOME s2) ∧
  sub_completion n next_uvar s2 ts s3
  ⇒
  sub_completion n next_uvar s1 ((t1,t2)::ts) s3`,
rw [sub_completion_def, pure_add_constraints_def]);

val sub_completion_infer = Q.prove (
`!menv cenv env e st1 t st2 n ts2 s.
  (infer_e menv cenv env e st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
rw [sub_completion_def, pure_add_constraints_append] >>
imp_res_tac infer_e_constraints >>
imp_res_tac infer_e_next_uvar_mono >>
qexists_tac `ts` >>
rw [] >|
[qexists_tac `st2.subst` >>
     rw [],
 full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]]);

val sub_completion_add_constraints = Q.prove (
`!s1 ts1 s2 n next_uvar s2 s3 ts2.
  pure_add_constraints s1 ts1 s2 ∧
  sub_completion n next_uvar s2 ts2 s3
  ⇒
  sub_completion n next_uvar s1 (ts1++ts2) s3`,
induct_on `ts1` >>
rw [pure_add_constraints_def] >>
Cases_on `h` >>
fs [pure_add_constraints_def] >>
res_tac >>
fs [sub_completion_def] >>
rw [] >>
fs [pure_add_constraints_def, pure_add_constraints_append] >>
metis_tac []);

val sub_completion_more_vars = Q.prove (
`!m n1 n2 s1 ts s2.
  sub_completion m (n1 + n2) s1 ts s2 ⇒ sub_completion m n1 s1 ts s2`,
rw [sub_completion_def] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]);

val sub_completion_infer_es = Q.prove (
`!menv cenv env es st1 t st2 n ts2 s.
  (infer_es menv cenv env es st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `es` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
res_tac >>
imp_res_tac sub_completion_infer >>
metis_tac [APPEND_ASSOC]);

val sub_completion_infer_p = Q.prove (
`(!cenv p st t env st' tvs extra_constraints s.
    (infer_p cenv p st = (Success (t,env), st')) ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s) ∧
 (!cenv ps st ts env st' tvs extra_constraints s.
    (infer_ps cenv ps st = (Success (ts,env), st')) ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s)`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
fs [] >|
[metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars],
 imp_res_tac sub_completion_add_constraints >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [APPEND_ASSOC]]);

val sub_completion_infer_pes = Q.prove (
`!menv cenv env pes t1 t2 st1 t st2 n ts2 s.
  (infer_pes menv cenv env pes t1 t2 st1 = (Success (), st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `pes` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
PairCases_on `v'` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
res_tac >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer_p >>
fs [] >>
metis_tac [APPEND, APPEND_ASSOC]);

val sub_completion_infer_funs = Q.prove (
`!menv cenv env funs st1 t st2 n ts2 s.
  (infer_funs menv cenv env funs st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `funs` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
res_tac >>
imp_res_tac sub_completion_infer >>
fs [] >>
metis_tac [sub_completion_more_vars, APPEND_ASSOC]);

val sub_completion_apply = Q.prove (
`!n uvars s1 ts s2 t1 t2.
  t_wfs s1 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2) ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
cases_on `h` >>
fs [pure_add_constraints_def] >>
fs [] >>
metis_tac [t_unify_apply2, t_unify_wfs]);

val sub_completion_apply_list = Q.prove (
`!n uvars s1 ts s2 ts1 ts2.
  t_wfs s1 ∧
  (MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2) ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  (MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2)`,
induct_on `ts1` >>
rw [] >>
cases_on `ts2` >>
fs [] >>
metis_tac [sub_completion_apply]);

val sub_completion_wfs = Q.prove (
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

val check_t_to_check_freevars = Q.store_thm ("check_t_to_check_freevars",
`!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
fs [EVERY_MEM]);

val sub_completion_check = Q.prove (
`!tvs m s uvar s' extra_constraints.
sub_completion m (uvar + tvs) s' extra_constraints s
⇒
EVERY (λn. check_freevars m [] (convert_t (t_walkstar s (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)`,
induct_on `tvs` >>
rw [sub_completion_def, COUNT_LIST_SNOC, EVERY_SNOC] >>
fs [sub_completion_def] >|
[qpat_assum `!m' s. P m' s` match_mp_tac >>
     rw [] >>
     qexists_tac `s'` >>
     qexists_tac `extra_constraints` >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF],
 fs [SUBSET_DEF] >>
     `uvar+tvs < uvar + SUC tvs`
            by full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
     metis_tac [check_t_to_check_freevars]]);

val t_walkstar_eqn1 = Q.prove (
`!s idx ts tc.
  t_wfs s ⇒ 
  (t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx) ∧
  (t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP (t_walkstar s) ts) tc)`,
rw [t_walkstar_eqn, t_walk_eqn]);

val check_t_subst = Q.prove (
`!t tvs s. 
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw []);

val check_t_deBruijn_inc2 = Q.prove (
`!inc t. check_t tvs {} t ⇒ check_t (inc + tvs) {} (infer_deBruijn_inc inc t)`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [check_t_def, infer_deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM]);

val infer_deBruijn_inc0 = Q.prove (
`!(n:num) t. infer_deBruijn_inc 0 t = t`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val infer_deBruijn_inc0_id = Q.prove (
`infer_deBruijn_inc 0 = (\x.x)`,
metis_tac [infer_deBruijn_inc0]);

val convert_inc = Q.prove (
`!t tvs tvs'. 
  check_t tvs' {} t
  ⇒
  (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
rw [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
induct_on `ts` >>
fs [] >>
metis_tac []);

val db_subst_infer_subst_swap = Q.prove (
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

val subst_infer_subst_swap = Q.prove (
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
rw [type_subst_def, infer_type_subst_def, t_walkstar_eqn1] >|
[full_case_tac >>
     full_case_tac >>
     rw [t_walkstar_eqn1] >>
     fs [lookup_notin] >>
     imp_res_tac lookup_in2 >>
     fs [MAP_ZIP, LENGTH_COUNT_LIST] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`uvar`,`uvar`) >>
     induct_on `tvs` >>
     fs [lookup_def] >>
     rw [COUNT_LIST_def, MAP_MAP_o, combinTheory.o_DEF] >>
     qpat_assum `!uvar. P uvar` (mp_tac o Q.SPEC `SUC uvar`) >>
     rw [] >>
     fs [DECIDE ``!(x:num) y. (x + SUC y) = ((SUC x) + y)``],
 metis_tac []]);

val convert_t_subst = Q.prove (
`(!t tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    check_freevars 0 tvs t ⇒
    convert_t (infer_type_subst (ZIP (tvs,ts')) t) = 
    type_subst (ZIP (tvs, MAP convert_t ts')) t) ∧
 (!ts tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    EVERY (check_freevars 0 tvs) ts ⇒
    MAP convert_t (MAP (infer_type_subst (ZIP (tvs,ts'))) ts) = 
    MAP (type_subst (ZIP (tvs, MAP convert_t ts'))) ts)`,
ho_match_mp_tac t_induction >>
rw [check_freevars_def, convert_t_def, type_subst_def, infer_type_subst_def] >|
[full_case_tac >>
     full_case_tac >>
     fs [lookup_notin] >>
     imp_res_tac lookup_in2 >>
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

val check_env_bind = Q.prove (
`!uvs x tvs t env.
  check_env uvs (bind x (tvs,t) env) = (check_t tvs uvs t ∧ check_env uvs env)`,
rw [check_env_def, bind_def]);

val check_env_lookup = Q.prove (
`!uvs n env tvs t.
  check_env uvs env ∧
  (lookup n env = SOME (tvs,t))
  ⇒
  check_t tvs uvs t`,
induct_on `env` >>
rw [check_t_def, lookup_def] >>
PairCases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
rw [] >>
fs [check_env_bind, GSYM bind_def] >>
metis_tac []);

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
   (lookup x env = SOME (tvs,t)) ⇒
   ((lookup_tenv x 0 tenv = 
     SOME (tvs, convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))))`;

val tenv_inv_empty_to = Q.prove (
`!s env tenv.
  t_wfs s ∧ check_env {} env ∧ tenv_inv FEMPTY env tenv 
  ⇒ 
  tenv_inv s env tenv`,
induct_on `env` >>
rw [tenv_inv_def] >>
imp_res_tac check_env_lookup >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = x` >>
fs [] >>
rw [GSYM check_t_subst] >>
metis_tac [t_walkstar_FEMPTY]);

val check_t_deBruijn_inc = Q.prove (
`!inc t. check_t 0 UNIV t ⇒ (infer_deBruijn_inc inc t = t)`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [check_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val check_menv_lookup = Q.prove (
`!menv mn n env tvs t.
  check_menv menv ∧
  (lookup mn menv = SOME env) ∧
  (lookup n env = SOME (tvs,t))
  ⇒
  check_t tvs {} t`,
induct_on `menv` >>
rw [lookup_def, check_t_def, check_menv_def] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = mn` >>
fs [] >>
rw [] >|
[induct_on `env` >>
     fs [lookup_def] >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0 = n` >>
     fs [],
 metis_tac [check_menv_def]]);

val check_cenv_lookup = Q.prove (
`!cenv cn tvs ts t.
  check_cenv cenv ∧
  (lookup cn cenv = SOME (tvs,ts,t))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
induct_on `cenv` >>
rw [] >>
PairCases_on `h` >>
fs [check_cenv_def] >>
every_case_tac >>
rw [] >>
metis_tac []);

val t_vwalk_check = Q.prove (
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

val t_walkstar_check = Q.prove (
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
[qpat_assum `t_unify s t1 t2 = SOME s'` mp_tac >>
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

val t_unify_check_s = Q.prove (
`!s1 tvs uvs t1 t2 s2.
  t_wfs s1 ∧
  check_s tvs uvs s1 ∧ 
  check_t tvs uvs t1 ∧
  check_t tvs uvs t2 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  check_s tvs uvs s2`,
metis_tac [t_unify_check_s_help]);

val pure_add_constraints_check_s = Q.prove (
`!s1 tvs uvs ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2 ∧
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

val infer_p_check_t = Q.prove (
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
rw [check_t_def] >|
[PairCases_on `v'` >>
     fs [remove_pair_lem, EVERY_MEM] >>
     rw [] >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
     rw [check_t_def] >>
     `?n. st'.next_uvar = st'''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st'''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
     rw [check_t_def] >>
     decide_tac,
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [infer_p_wfs],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MEM] >>
     rw [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
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
rw [check_freevars_def, check_t_def, infer_type_subst_def] >|
[pop_assum mp_tac >>
     Q.SPEC_TAC (`uvs`, `uvs`) >>
     induct_on `tvs` >>
     rw [COUNT_LIST_def, check_t_def] >>
     qpat_assum `!uvs. P uvs` (mp_tac o Q.SPEC `SUC uvs`) >>
     rw [MAP_MAP_o, combinTheory.o_DEF] >>
     fs [DECIDE ``SUC a + b = a + SUC b``],
 metis_tac [EVERY_MAP]]);

val infer_p_check_s = Q.prove (
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
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [] >|
[metis_tac [check_s_more],
 PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono],
 PairCases_on `v''` >>
     fs [] >>
     res_tac >>
     imp_res_tac infer_p_wfs >>
     `st'''.next_uvar ≤ st'''.next_uvar + LENGTH (FST v')` by decide_tac >>
     `check_s tvs (count st'.next_uvar) st'''.subst` by metis_tac [check_s_more2] >>
     match_mp_tac pure_add_constraints_check_s >>
     qexists_tac `st'''.subst` >>
     qexists_tac `(ZIP (v''0, MAP (infer_type_subst (ZIP (FST v', MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH (FST v')))))) (FST (SND v'))))` >>
     rw [] >>
     rw [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
     metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_p_next_uvar_mono,
                arithmeticTheory.LESS_EQ_TRANS, infer_p_check_t] >>
     PairCases_on `v'` >>
     fs [] >>
     imp_res_tac check_cenv_lookup >>
     imp_res_tac check_infer_type_subst >>
     rw [] >>
     fs [EVERY_MEM] >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM],
 PairCases_on `v'` >>
     metis_tac [check_s_more2, infer_p_next_uvar_mono],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     metis_tac [infer_p_wfs, check_s_more2, infer_p_next_uvar_mono]]);

val check_env_more = Q.prove (
`!uvs env. check_env (count uvs) env ⇒ !uvs'. uvs ≤ uvs' ⇒ check_env (count uvs') env`,
rw [check_env_def, EVERY_MEM] >>
PairCases_on `e` >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [check_t_more4]);

val check_env_merge = Q.prove (
`!uvs env1 env2. check_env uvs (merge env1 env2) = (check_env uvs env1 ∧ check_env uvs env2)`,
rw [check_env_def, merge_def]);

val check_env_letrec_lem = Q.prove (
`∀uvs funs uvs' n.
  check_env (count uvs) (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (uvs' + n)) (COUNT_LIST (LENGTH funs)))) =
  ((funs = []) ∨ (uvs' + LENGTH funs ≤ uvs))`,
induct_on `funs` >>
rw [COUNT_LIST_def, check_env_def] >>
cases_on `funs` >>
fs [COUNT_LIST_def, check_env_def] >>
PairCases_on `h` >>
rw [check_t_def] >-
decide_tac >>
rw [] >>
PairCases_on `h'` >>
fs [check_t_def] >>
eq_tac >>
srw_tac [ARITH_ss] [] >>
fs [MAP_MAP_o, combinTheory.o_DEF] >|
[qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     rw [] >>
     fs [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``] >>
     decide_tac,
 qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     rw [] >>
     fs [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``,
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
rw [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST, 
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >>
metis_tac []);

val infer_e_check_t = Q.prove (
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
rw [infer_e_def, success_eqns, remove_pair_lem] >>
fs [check_t_def] >>
imp_res_tac infer_e_next_uvar_mono >>
fs [EVERY_MAP, check_t_def, check_env_bind, check_env_merge, check_t_infer_db_subst] >|
[metis_tac [check_t_more4],
 PairCases_on `v'` >>
     imp_res_tac check_env_lookup >>
     rw [] >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     imp_res_tac check_menv_lookup >>
     rw [] >>
     metis_tac [check_t_more],
 metis_tac [check_t_more4],
 rw [EVERY_MEM, MEM_COUNT_LIST] >>
     decide_tac,
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 metis_tac [check_t_more4],
 res_tac >>
     fs [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 decide_tac,
 res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 res_tac >>
     fs [check_env_merge, check_env_letrec_lem] >>
     metis_tac [check_env_more, DECIDE ``x + y ≤ z ⇒ x ≤ z:num``],
 res_tac >>
     fs [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, check_t_more4, DECIDE ``x ≤ x + 1:num``]]);

val infer_e_check_s = Q.prove (
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
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [] >|
[`t_wfs st''.subst` by (metis_tac [infer_e_wfs]) >>
     match_mp_tac check_s_more >>
     match_mp_tac t_unify_check_s >>
     qexists_tac `st''.subst` >>
     qexists_tac `t2` >>
     qexists_tac `Infer_Tapp [] TC_exn` >>
     rw [check_t_def] >>
     metis_tac [infer_e_check_t, arithmeticTheory.ADD_0, check_t_more2],
 `t_wfs st''.subst ∧
  check_env (count (st'' with next_uvar := st''.next_uvar).next_uvar) env`
               by metis_tac [check_env_more, infer_e_next_uvar_mono, infer_e_wfs, infer_st_rewrs] >>
     `check_s tvs (count (st'' with next_uvar := st''.next_uvar).next_uvar) (st'' with next_uvar := st''.next_uvar).subst`
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar).next_uvar) t`
               by metis_tac [check_t_more4, infer_e_check_t, infer_st_rewrs] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar).next_uvar) (Infer_Tapp [] TC_exn)`
                  by rw [check_t_def] >>
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
     rw [] >>
     rw [EVERY_CONJ, every_shim2, every_zip_fst, every_zip_snd, EVERY_MAP] >-
     metis_tac [check_t_more2, arithmeticTheory.ADD_0, check_t_more4, infer_e_next_uvar_mono,
                arithmeticTheory.LESS_EQ_TRANS, infer_e_check_t] >>
     PairCases_on `v'` >>
     fs [] >>
     imp_res_tac check_cenv_lookup >>
     imp_res_tac check_infer_type_subst >>
     rw [] >>
     fs [EVERY_MEM] >>
     metis_tac [check_t_more2, arithmeticTheory.ADD_0,arithmeticTheory.ADD_COMM],
 qpat_assum `!t1. P t1` match_mp_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`Infer_Tuvar st.next_uvar`, `st with next_uvar := st.next_uvar + 1`, `t2`] >>
     rw [check_s_more, check_env_bind, check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``],
 metis_tac [],
 `t_wfs st''.subst ∧ 
  check_env (count st''.next_uvar) env ∧ 
  check_t 0 (count st''.next_uvar) t'` 
          by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     `check_t 0 (count (st''.next_uvar + 1)) t'` 
             by metis_tac [check_t_more4, DECIDE ``x ≤ x + 1:num``] >>
     `check_t 0 (count (st''.next_uvar + 1)) (Infer_Tapp [Infer_Tuvar st''.next_uvar] TC_ref)` 
             by rw [check_t_def] >>
     metis_tac [t_unify_check_s, check_s_more, arithmeticTheory.ADD_0, check_t_more2],
 fs [] >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_int)` by rw [check_t_def] >>
     `t_wfs st'''.subst ∧ 
      t_wfs st''.subst ∧ 
      check_env (count st'''.next_uvar) env ∧
      check_env (count st''.next_uvar) env ∧
      check_t 0 (count st'''.next_uvar) t1 ∧
      check_t 0 (count st'''.next_uvar) t2` 
              by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     `check_s tvs (count st'''.next_uvar) s`
                    by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 fs [] >>
     `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_int)` by rw [check_t_def] >>
     `t_wfs st'''.subst ∧ 
      t_wfs st''.subst ∧ 
      check_env (count st'''.next_uvar) env ∧
      check_env (count st''.next_uvar) env ∧
      check_t 0 (count st'''.next_uvar) t1 ∧
      check_t 0 (count st'''.next_uvar) t2` 
              by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     `check_s tvs (count st'''.next_uvar) s`
                    by metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0] >>
     metis_tac [t_unify_wfs, t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 `t_wfs st''.subst ∧ 
  t_wfs st'''.subst ∧ 
  check_env (count st''.next_uvar) env ∧ 
  check_t 0 (count st'''.next_uvar) t1 ∧
  check_t 0 (count st'''.next_uvar) t2`
          by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 `t_wfs st'''.subst ∧ 
  t_wfs st''.subst ∧ 
  check_env (count st''.next_uvar) env ∧
  check_env (count (st'''.next_uvar)) env ∧
  check_env (count (st'''.next_uvar + 1)) env ∧
  check_t 0 (count (st'''.next_uvar)) t1 ∧
  check_t 0 (count (st'''.next_uvar)) t2` 
              by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono,
                            DECIDE ``x ≤ y ⇒ x ≤ y + 1:num``] >>
     `check_t 0 (count (st'''.next_uvar + 1)) t1 ∧ 
      check_t 0 (count (st'''.next_uvar + 1)) t2` 
                  by metis_tac [check_t_more3] >>
     `check_t 0 (count (st'''.next_uvar + 1)) (Infer_Tapp [t2; Infer_Tuvar st'''.next_uvar] TC_fn)`
              by rw [check_t_def] >>
     `check_s tvs (count (st'''.next_uvar + 1)) st'''.subst`
             by metis_tac [check_s_more] >>
     metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 `t_wfs st'''.subst ∧ 
  t_wfs st''.subst ∧ 
  check_env (count st''.next_uvar) env ∧
  check_env (count (st'''.next_uvar)) env ∧
  check_t 0 (count (st'''.next_uvar)) t1 ∧
  check_t 0 (count (st'''.next_uvar)) t2` 
              by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
     `check_t 0 (count st'''.next_uvar) (Infer_Tapp [t2] TC_ref)`
              by rw [check_t_def] >>
     metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_bool)` by rw [check_t_def] >>
     `t_wfs st'''.subst ∧ 
      t_wfs st''.subst ∧ 
      check_env (count st''.next_uvar) env ∧
      check_env (count (st'''.next_uvar)) env ∧
      check_t 0 (count (st'''.next_uvar)) t1 ∧
      check_t 0 (count (st'''.next_uvar)) t2` 
                  by metis_tac [check_t_more4, infer_e_check_t, infer_e_wfs, check_env_more, infer_e_next_uvar_mono] >>
      fs [] >>
      `check_s tvs (count st'''.next_uvar) st'''.subst` by metis_tac [] >>
      `t_wfs s` by metis_tac [t_unify_wfs] >>
      metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0],
 `!uvs tvs. check_t tvs uvs (Infer_Tapp [] TC_bool)` by rw [check_t_def] >>
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
     `check_s tvs (count st''.next_uvar) s` 
             by metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0, infer_st_rewrs] >>
     `check_s tvs (count st''''.next_uvar) st''''.subst` by metis_tac [infer_st_rewrs] >>
     `check_s tvs (count st'''''.next_uvar) st'''''.subst` by metis_tac [] >>
     metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0, infer_st_rewrs],
 `t_wfs st''.subst ∧
  check_env (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) env`
               by metis_tac [check_env_more, infer_e_next_uvar_mono, infer_e_wfs, DECIDE ``x ≤ x + 1:num``,
                             infer_st_rewrs] >>
     `check_s tvs (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) (st'' with next_uvar := st''.next_uvar + 1).subst`
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) t1`
               by metis_tac [check_t_more4, infer_e_check_t, infer_st_rewrs, DECIDE ``x ≤ x + 1:num``] >>
     `check_t 0 (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) (Infer_Tuvar st''.next_uvar)`
                  by rw [check_t_def] >>
     qpat_assum `!t1 t2 st st' tvs. P t1 t2 st st' tvs` match_mp_tac >>
     metis_tac [infer_st_rewrs, check_s_more],
 `check_env (count st''.next_uvar) (bind x (0,t1) env)`
         by (rw [check_env_bind] >>
             metis_tac [infer_e_check_t, check_env_more, infer_e_next_uvar_mono]) >>
     metis_tac [infer_e_wfs],
 `check_env (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar)
            (merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))) env)`
                 by (rw [check_env_merge] >>
                     rw [check_env_letrec_lem] >>
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
                     rw [EVERY_CONJ, every_shim2, every_zip_snd, every_zip_fst, LENGTH_COUNT_LIST, EVERY_MAP,
                         every_count_list, check_t_def] >|
                     [`st.next_uvar + LENGTH funs ≤ st'''.next_uvar` by metis_tac [infer_st_rewrs, infer_e_next_uvar_mono] >>
                          decide_tac,
                      metis_tac [infer_e_check_t, check_t_more2, arithmeticTheory.ADD_0]]) >>
     `t_wfs st''''.subst` by metis_tac [pure_add_constraints_wfs] >>
     `check_env (count st''''.next_uvar)
            (merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))) env)`
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
     fs [] >>
     `check_s tvs (count st''.next_uvar) s` 
                  by metis_tac [t_unify_check_s, check_t_more2, arithmeticTheory.ADD_0, infer_p_next_uvar_mono,
                                check_t_more4] >>
     `check_env (count st''.next_uvar) (merge (MAP (λ(n,t). (n,0,t)) v'1) env)`
              by (rw [check_env_merge] >>
                  rw [check_env_def, EVERY_MAP, LAMBDA_PROD]) >>
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
 `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) (bind x (0,Infer_Tuvar st.next_uvar) env)`
               by (rw [check_env_bind, check_t_def] >>
                   metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
     `check_s tvs (count (st with next_uvar := st.next_uvar + 1).next_uvar) (st with next_uvar := st.next_uvar + 1).subst` 
               by metis_tac [infer_st_rewrs, check_s_more] >>
     `t_wfs (st with next_uvar := st.next_uvar + 1).subst` by rw [] >>
     `check_s tvs (count st'''.next_uvar) st'''.subst ∧ t_wfs st'''.subst` 
               by metis_tac [infer_e_wfs]  >>
     `check_env (count st'''.next_uvar) env` 
               by metis_tac [infer_e_next_uvar_mono, check_env_more, infer_st_rewrs, DECIDE ``x ≤ x + 1:num``] >>
     metis_tac []]);

val tenv_inv_extend = Q.prove (
`!s x tvs t env t' tenv.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,tvs,t)::env) (bind_tenv x tvs (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)) tenv)`,
rw [tenv_inv_def] >>
every_case_tac >>
rw [] >>
rw [lookup_tenv_def, bind_tenv_def, deBruijn_inc0] >>
metis_tac []);

val tenv_inv_extend0 = Q.prove (
`!s x t env tenv.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,0,t)::env) (bind_tenv x 0 (convert_t (t_walkstar s t)) tenv)`,
rw [] >>
`infer_deBruijn_inc 0 o_f s = s` by rw [GSYM fmap_EQ_THM, infer_deBruijn_inc0] >>
metis_tac [tenv_inv_extend]);

val inc_convert_t = Q.prove (
`(!t tvs' tvs. check_t tvs' {} t ⇒ (deBruijn_inc tvs' tvs (convert_t t) = convert_t t)) ∧
 (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ⇒ (MAP (deBruijn_inc tvs' tvs o convert_t) ts = MAP convert_t ts))`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, convert_t_def, deBruijn_inc_def] >>
metis_tac [MAP_MAP_o]);

val tenv_inv_extend_tvar_empty_subst = Q.prove (
`!env tvs tenv.
  check_env {} env ∧ tenv_inv FEMPTY env tenv ⇒ tenv_inv FEMPTY env (bind_tvar tvs tenv)`,
induct_on `env` >>
fs [tenv_inv_def] >>
rw [] >>
PairCases_on `h` >>
rw [bind_tvar_def, lookup_tenv_def] >>
fs [t_walkstar_FEMPTY] >>
res_tac >>
imp_res_tac lookup_tenv_inc >>
fs [] >>
`check_t h1 {} h2 ∧ check_env {} env` by fs [check_env_def] >>
cases_on `h0 = x` >>
fs [] >>
rw [] >>
imp_res_tac check_env_lookup >>
metis_tac [inc_convert_t]);

val tenv_inv_letrec_merge = Q.prove (
`!funs tenv' env tenv st s.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s (merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))) env)
             (bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))) tenv)`,
induct_on `funs` >>
rw [COUNT_LIST_def, merge_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def] >>
match_mp_tac tenv_inv_extend0 >>
fs [merge_def] >>
rw [check_t_def] >>
res_tac >>
pop_assum (mp_tac o Q.SPEC `st with next_uvar := st.next_uvar + 1`) >>
strip_tac >>
fs [] >>
metis_tac [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]);

val convert_env_def = Define `
convert_env s env = MAP (\(x,t). (x, convert_t (t_walkstar s t))) env`;

val tenv_inv_merge = Q.prove (
`!s x uv env env' tenv. 
  tenv_inv s env tenv
  ⇒
  tenv_inv s (merge (MAP (λ(n,t). (n,0,t)) env') env) (bind_var_list 0 (convert_env s env') tenv)`,
induct_on `env'` >>
rw [merge_def, convert_env_def, bind_var_list_def] >>
res_tac >>
fs [tenv_inv_def] >>
rw [] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = x` >>
fs [] >>
rw [bind_var_list_def, bind_tenv_def, lookup_def, lookup_tenv_def,
    deBruijn_inc0, infer_deBruijn_inc0_id, o_f_id] >>
fs [merge_def] >>
res_tac >>
metis_tac [convert_env_def]);

val letrec_lemma = Q.prove (
`!funs funs_ts s st. 
  (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)) =
   MAP (\t. convert_t (t_walkstar s t)) funs_ts)
  ⇒
  (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs))) =
   MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts)`,
induct_on `funs` >>
rw [] >>
cases_on `funs_ts` >>
fs [COUNT_LIST_def] >>
rw [] >|
[PairCases_on `h` >>
     rw [],
 qpat_assum `!x. P x` match_mp_tac >>
     qexists_tac `st with next_uvar := st.next_uvar + 1` >>
     fs [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]]);

val check_t_walkstar = Q.prove (
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
rw [check_t_def, t_walkstar_eqn1, EVERY_MAP] >>
metis_tac []);

val infer_funs_length = Q.prove (
`!menv cenv env funs ts st1 st2.
  (infer_funs menv cenv env funs st1 = (Success ts, st2)) ⇒
  (LENGTH funs = LENGTH ts)`,
induct_on `funs` >>
rw [infer_e_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
metis_tac []);

val map_zip_lem = Q.prove (
`!funs ts. 
  (LENGTH funs = LENGTH ts)
  ⇒
  (MAP (λx. FST ((λ((x',y,z),t). (x',convert_t (t_walkstar s t))) x)) (ZIP (funs,ts))
   =
   MAP FST funs)`,
induct_on `funs` >>
rw [] >>
cases_on `ts` >>
fs [] >>
PairCases_on `h` >>
rw []);

val type_pes_def = Define `
type_pes menv cenv tenv pes t1 t2 =
  ∀x::set pes.
    (λ(p,e).
       ∃tenv'.
         ALL_DISTINCT (pat_bindings p []) ∧
         type_p (num_tvs tenv) cenv p t1 tenv' ∧
         type_e menv cenv (bind_var_list 0 tenv' tenv) e t2) x`;

val type_pes_cons = Q.prove (
`!menv cenv tenv p e pes t1 t2.
  type_pes menv cenv tenv ((p,e)::pes) t1 t2 =
  (ALL_DISTINCT (pat_bindings p []) ∧
   (?tenv'.
       type_p (num_tvs tenv) cenv p t1 tenv' ∧
       type_e menv cenv (bind_var_list 0 tenv' tenv) e t2) ∧
   type_pes menv cenv tenv pes t1 t2)`,
rw [type_pes_def, RES_FORALL] >>
eq_tac >>
rw [] >>
rw [] >|
[pop_assum (mp_tac o Q.SPEC `(p,e)`) >>
     rw [],
 pop_assum (mp_tac o Q.SPEC `(p,e)`) >>
     rw [] >>
     metis_tac [],
 metis_tac []]);

val infer_p_bindings = Q.prove (
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
rw [] >|
[PairCases_on `v'` >>
     rw [] >>
     metis_tac [],
 PairCases_on `v''` >>
     rw [] >>
     metis_tac [],
 PairCases_on `v'` >>
     rw [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     rw [] >>
     metis_tac [APPEND_ASSOC]]);

val infer_p_sound = Q.prove (
`(!cenv p st t env st' tvs extra_constraints s.
    (infer_p cenv p st = (Success (t,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_p tvs cenv p (convert_t (t_walkstar s t)) (convert_env s env)) ∧
 (!cenv ps st ts env st' tvs extra_constraints s.
    (infer_ps cenv ps st = (Success (ts,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_ps tvs cenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env))`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [Once type_p_cases, convert_env_def] >>
imp_res_tac sub_completion_wfs >>
fs [] >>
rw [t_walkstar_eqn1, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|
[match_mp_tac check_t_to_check_freevars >>
     rw [] >>
     fs [sub_completion_def] >>
     qpat_assum `!uv. uv ∈ FDOM s ⇒ P uv` match_mp_tac >>
     fs [count_def, SUBSET_DEF],
 `?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [infer_p_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     fs [convert_env_def] >>
     metis_tac [MAP_MAP_o],
 `?ts env. v'' = (ts,env)` by (PairCases_on `v''` >> metis_tac []) >>
     `?tvs ts tn. v' = (tvs,ts,tn)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `type_ps tvs cenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env)` 
               by metis_tac [sub_completion_add_constraints, sub_completion_more_vars] >>
     rw [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_p_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, LENGTH_COUNT_LIST] >>
     fs [] >-
     metis_tac [sub_completion_check] >>
     `t_wfs st'''.subst` by metis_tac [infer_p_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     pop_assum (fn _ => all_tac) >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     rw [MAP_ZIP] >>
     `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
     imp_res_tac sub_completion_apply_list >>
     NTAC 6 (pop_assum (fn _ => all_tac)) >>
     pop_assum mp_tac >>
     rw [subst_infer_subst_swap] >>
     `EVERY (check_freevars 0 tvs') ts'` by metis_tac [check_cenv_lookup] >>
     rw [] >>
     fs [convert_env_def] >>
     metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF],
 `?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [infer_p_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     fs [convert_env_def] >>
     metis_tac [],
 `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `?ts' env'. v'' = (ts',env')` by (PairCases_on `v''` >> metis_tac []) >>
     rw [] >>
     `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
     `?ts. sub_completion tvs st''.next_uvar st''.subst ts s` by metis_tac [sub_completion_infer_p] >>
     fs [convert_env_def] >>
     metis_tac []]);

val infer_subst_def = tDefine "infer_subst" `
(infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n) ∧
(infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst s) ts) tc) ∧
(infer_subst s (Infer_Tuvar n) =
  case FLOOKUP s n of
      NONE => Infer_Tuvar n
    | SOME m => Infer_Tvar_db m)`
(wf_rel_tac `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 srw_tac[ARITH_ss] [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val infer_subst_FEMPTY = Q.prove (
`(!t. infer_subst FEMPTY t = t) ∧
 (!ts. MAP (infer_subst FEMPTY) ts = ts)`,
ho_match_mp_tac infer_t_induction >>
rw [SUBSET_DEF, infer_subst_def] >>
metis_tac []);

val infer_subst_submap = Q.prove (
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

val generalise_subst = Q.prove (
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
     qpat_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `tvs'+n`, `s''`, `tvs''`, `s'''`, `ts''`]) >>
     qpat_assum `!m'. P m'`
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
               decide_tac,
           res_tac >>
               rw [INTER_UNION] >>
               fs [SUBMAP_DEF] >>
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

val generalise_subst_empty = Q.prove (
`!ts tvs s ts'.
  (generalise_list 0 0 FEMPTY ts = (tvs, s, ts'))
  ⇒
  (FDOM s = { uv | uv ∈ BIGUNION (set (MAP t_vars ts)) }) ∧
  (!uv. uv ∈ FDOM s ⇒ ∃tv. (FAPPLY s uv = tv) ∧ tv < tvs) ∧
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

val binop_tac =
imp_res_tac infer_e_wfs >>
imp_res_tac t_unify_wfs >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fs [] >>
res_tac >>
fs [] >>
imp_res_tac t_unify_apply >>
imp_res_tac sub_completion_apply >>
imp_res_tac t_unify_wfs >>
imp_res_tac sub_completion_wfs >>
fs [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def] >>
rw [type_op_cases, Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def, Texn_def] >>
metis_tac [MAP, infer_e_next_uvar_mono, check_env_more];

val infer_e_sound = Q.prove (
`(!menv cenv env e st st' tenv t extra_constraints s.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_e (convert_menv menv) cenv tenv e 
           (convert_t (t_walkstar s t))) ∧
 (!menv cenv env es st st' tenv ts extra_constraints s.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_es (convert_menv menv) cenv tenv es 
            (MAP (convert_t o t_walkstar s) ts)) ∧
 (!menv cenv env pes t1 t2 st st' tenv extra_constraints s.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_pes (convert_menv menv) cenv tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s t2))) ∧
 (!menv cenv env funs st st' tenv extra_constraints s ts.
    (infer_funs menv cenv env funs st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    type_funs (convert_menv menv) cenv tenv funs (MAP2 (\(x,y,z) t. (x, (convert_t o t_walkstar s) t)) funs ts))`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >>
fs [bind_def, check_t_def, check_env_bind, check_env_merge] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [Tbool_def, Tint_def, Tunit_def] >|
[cheat,
 cheat,
 cheat,
 cheat,
 (*
 (* Raise *)
     fs [sub_completion_def, flookup_thm, count_add1, SUBSET_DEF] >>
     `st.next_uvar < st.next_uvar + 1` by decide_tac >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],
 (* Handle *)
     binop_tac,
 (* Handle *)
     `tenv_inv s
                 ((x,0,Infer_Tapp [] TC_int)::env) 
                 (bind_tenv x 0 
                            (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) 
                            tenv)`
             by (match_mp_tac tenv_inv_extend0 >>
                 rw []) >>
     `num_tvs tenv = num_tvs (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) tenv)`
             by rw [bind_tenv_def, num_tvs_def] >>
     fs [bind_tenv_def] >>
     `check_env (count st''.next_uvar) env`
                by (fs [] >>
                    metis_tac [check_env_more, infer_e_next_uvar_mono]) >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac sub_completion_unify2 >>
     `t_wfs (st''' with subst := s').subst`
                  by (rw [] >> metis_tac [t_unify_wfs]) >>
     `type_e (convert_menv menv) cenv (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) tenv) e'
             (convert_t (t_walkstar s t2))` 
                   by metis_tac [] >>
     `t_wfs s` by metis_tac [t_unify_wfs, sub_completion_wfs] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s'` by metis_tac [t_unify_wfs] >>
     `t_walkstar s t = t_walkstar s t2` by metis_tac [sub_completion_apply] >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def],
     *)
 (* Lit bool *)
     binop_tac,
 (* Lit int *)
     binop_tac,
 (* Lit unit *)
     binop_tac,
 (* Var short *)
     rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)` 
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     qexists_tac `convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)` >>
     qexists_tac `MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `count st.next_uvar ⊆ FDOM s`
                  by (fs [count_def, SUBSET_DEF] >>
                      rw [] >>
                      metis_tac [DECIDE ``x < y ⇒ x < y + z:num``]) >>
          `check_t tvs (FDOM s) t`
                     by metis_tac [check_env_lookup, check_t_more5] >>
          metis_tac [db_subst_infer_subst_swap, pure_add_constraints_wfs],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [LENGTH_COUNT_LIST] >>
          metis_tac [tenv_inv_def]],
 (* Var long *)
     rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)` 
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     qexists_tac `convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)` >>
     qexists_tac `MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `check_t tvs (FDOM s) t` by 
                     (metis_tac [check_menv_lookup, check_t_more]) >>
          metis_tac [db_subst_infer_subst_swap, pure_add_constraints_wfs],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [LENGTH_COUNT_LIST] >>
          fs [convert_menv_def, check_menv_def] >>
          `lookup mn (MAP (λ(mn,env). (mn,MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env)) menv) =
           SOME (MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env')`
                    by metis_tac [lookup_map] >>
          rw [] >>
          `lookup n (MAP (λ(x,y). (x,(\z. FST z,convert_t (SND z)) y)) env') =
           SOME ((\y. FST y,convert_t (SND y)) (tvs,t))`
                    by (match_mp_tac lookup_map >>
                        rw[]) >>
          fs [LAMBDA_PROD] >>
          `check_t tvs {} t`
                    by (imp_res_tac lookup_in >>
                        fs [MEM_MAP, EVERY_MEM] >>
                        rw [] >>
                        PairCases_on `y'` >>
                        PairCases_on `y''''` >>
                        PairCases_on `y'''` >>
                        PairCases_on `y'''''` >>
                        fs [] >>
                        rw [] >>
                        res_tac >>
                        fs [] >>
                        res_tac >>
                        fs []) >>
          metis_tac [check_t_subst, sub_completion_wfs]],
 (* Tup *)
     `?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     metis_tac [MAP_MAP_o],
 (* Con *)
     `?tvs ts t. v' = (tvs, ts, t)` by (PairCases_on `v'` >> rw []) >>
     rw [] >>
     fs [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, LENGTH_COUNT_LIST] >-
     metis_tac [sub_completion_check] >>
     `type_es (convert_menv menv) cenv tenv es (MAP (convert_t o t_walkstar s) ts'')`
             by (imp_res_tac sub_completion_add_constraints >>
                 `sub_completion (num_tvs tenv) st'''.next_uvar st'''.subst
                        (ZIP
                           (ts'',
                            MAP
                              (infer_type_subst
                                 (ZIP
                                    (tvs,
                                     MAP (λn. Infer_Tuvar (st'''.next_uvar + n))
                                       (COUNT_LIST (LENGTH tvs))))) ts) ++
                         extra_constraints) s`
                                   by metis_tac [sub_completion_more_vars] >>
                 imp_res_tac sub_completion_infer_es >>
                 metis_tac []) >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     pop_assum (fn _ => all_tac) >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     rw [MAP_ZIP] >>
     `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
     `MAP (t_walkstar s) ts'' =
       MAP (t_walkstar s)
         (MAP
            (infer_type_subst
               (ZIP
                  (tvs,
                   MAP (λn. Infer_Tuvar (st'''.next_uvar + n))
                     (COUNT_LIST (LENGTH tvs))))) ts)`
                 by metis_tac [sub_completion_apply_list] >>
     pop_assum mp_tac >>
     rw [subst_infer_subst_swap] >>
     `EVERY (check_freevars 0 tvs) ts` by metis_tac [check_cenv_lookup] >>
     metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF],
 (* Fun *)
     `t_wfs s ∧ t_wfs st'.subst` by metis_tac [infer_st_rewrs,sub_completion_wfs, infer_e_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >>
     imp_res_tac infer_e_next_uvar_mono >>
     fs [] >>
     `st.next_uvar < st'.next_uvar` by decide_tac >|
     [fs [sub_completion_def, SUBSET_DEF] >>
          metis_tac [check_t_to_check_freevars],
      `tenv_inv s
                 ((x,0,Infer_Tuvar st.next_uvar)::env) 
                 (bind_tenv x 0 
                            (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) 
                            tenv)`
             by (match_mp_tac tenv_inv_extend0 >>
                 fs []) >>
          fs [bind_tenv_def] >>
          `check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                     by rw [check_t_def] >>
          `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) env`
                     by (rw [] >>
                         metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
          metis_tac [num_tvs_def, infer_st_rewrs, bind_tenv_def]],
 (* Opref *)
     rw [type_uop_cases, Tref_def] >>
     binop_tac,
 (* Opderef *)
     rw [type_uop_cases, Tref_def] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_unify >>
     `t_wfs s'` by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs] >>
     fs [t_walkstar_eqn1] >>
     `type_e (convert_menv menv) cenv tenv e (convert_t (t_walkstar s t'))`
                by metis_tac [] >>
     metis_tac [convert_t_def, MAP],
 (* Opn *)
     binop_tac,
 (* Opb *)
     binop_tac,
 (* Equality *)
     binop_tac, 
 (* Opapp *)
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac sub_completion_unify >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [type_op_cases, Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def] >>
     qexists_tac `convert_t (t_walkstar s t2)` >>
     rw [] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_apply >>
     imp_res_tac t_unify_wfs >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def] >>
     metis_tac [check_env_more, infer_e_next_uvar_mono],
 (* Opassign *) 
     binop_tac, 
 (* Log *)
     binop_tac,
 (* Log *)
     binop_tac,
 (* If *)
     binop_tac,
 (* If *)
     imp_res_tac sub_completion_unify2 >>
     imp_res_tac sub_completion_infer >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify2 >>
     `type_e (convert_menv menv) cenv tenv e (convert_t (t_walkstar s t1))`
             by metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s'`  by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def],
 (* If *)
     `t_wfs (st'' with subst := s').subst` 
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with subst := s').next_uvar` 
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `check_env (count (st'' with subst := s').next_uvar) env` 
                by (metis_tac [check_env_more]) >>
     `?ts. sub_completion (num_tvs tenv) st'''''.next_uvar st'''''.subst ts s` 
               by metis_tac [sub_completion_unify2] >>
     imp_res_tac sub_completion_infer >>
     metis_tac [],
 (* If *)
     `t_wfs (st'' with subst := s').subst` 
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `t_wfs st''''.subst ∧ t_wfs st'''''.subst ∧ t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''''.next_uvar` 
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `check_env (count st''''.next_uvar) env` by metis_tac [check_env_more] >>
     `?ts. sub_completion (num_tvs tenv) st'''''.next_uvar st'''''.subst ts s` 
               by metis_tac [sub_completion_unify2] >>
     `type_e (convert_menv menv) cenv tenv e'' (convert_t (t_walkstar s t3))` by metis_tac [] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s''` by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     metis_tac [],
 (* Match *)
     `?ts. sub_completion (num_tvs tenv) st''.next_uvar st''.subst  ts s` 
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     `type_e (convert_menv menv) cenv tenv e (convert_t (t_walkstar s t1))` by metis_tac [] >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [RES_FORALL] >>
     `?p e. x = (p,e)` by (PairCases_on `x` >> metis_tac []) >>
     rw [] >>
     `t_wfs (st'' with next_uvar := st''.next_uvar + 1).subst`
              by (rw [] >>
                  metis_tac [infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with next_uvar := st''.next_uvar + 1).next_uvar`
              by (rw [] >>
                  imp_res_tac infer_e_next_uvar_mono >>
                  fs [] >>
                  decide_tac) >>
     `check_env (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) env` by metis_tac [check_env_more] >>
     `type_pes (convert_menv menv) cenv tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s (Infer_Tuvar st''.next_uvar)))`
              by metis_tac [] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [],
 (* Let *)
     disj2_tac >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [] >-
     metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_wfs >>
     `tenv_inv s ((x,0,t1)::env) 
                 (bind_tenv x 0 (convert_t (t_walkstar s t1)) tenv)` 
            by (match_mp_tac tenv_inv_extend0 >>
                rw [] >>
                fs []) >>
     `num_tvs (bind_tenv x 0 (convert_t (t_walkstar s t1)) tenv) = num_tvs tenv` 
            by (rw [num_tvs_def, bind_tenv_def]) >>
     `check_t 0 (count st''.next_uvar) t1` by metis_tac [infer_e_check_t] >>
     `check_env (count st''.next_uvar) env` by metis_tac [infer_e_next_uvar_mono, check_env_more] >>
     metis_tac [],
 (* Letrec *)
     `t_wfs (st with next_uvar := st.next_uvar + LENGTH funs).subst`
               by rw [] >>
     Q.ABBREV_TAC `env' = MAP2 (λ(f,x,e) uvar. (f,0:num,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))` >>
     Q.ABBREV_TAC `tenv' = MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))` >>
     `sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st'.next_uvar st'.subst extra_constraints s`
                 by metis_tac [num_tvs_bind_var_list] >>
     `?constraints1. sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st''''.next_uvar st''''.subst constraints1 s`
                 by metis_tac [sub_completion_infer] >>
     `?constraints2. sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st'''.next_uvar st'''.subst constraints2 s`
                 by metis_tac [sub_completion_add_constraints] >>
     `tenv_inv s (merge env' env) (bind_var_list 0 tenv' tenv)` 
                 by (UNABBREV_ALL_TAC >>
                     match_mp_tac tenv_inv_letrec_merge >>
                     rw []) >>
     `check_env (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar) (merge env' env)`
                 by (rw [check_env_merge] >|
                     [Q.UNABBREV_TAC `env'` >>
                          rw [check_env_letrec_lem],
                      metis_tac [check_env_more, DECIDE ``x ≤ x+y:num``]]) >>
     `type_funs (convert_menv menv) cenv (bind_var_list 0 tenv' tenv) funs 
                (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs funs_ts)`
                 by metis_tac [] >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs, pure_add_constraints_wfs] >>
     `st.next_uvar + LENGTH funs ≤ st''''.next_uvar`
                 by (fs [] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     metis_tac []) >>
     fs [] >>
     `type_e (convert_menv menv) cenv (bind_var_list 0 tenv' tenv) e (convert_t (t_walkstar s t))`
                 by metis_tac [check_env_more] >>
     qexists_tac `tenv'` >>
     qexists_tac `0` >>
     rw [bind_tvar_def] >>
     `tenv' = MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts`
                 by (Q.UNABBREV_TAC `tenv'` >>
                     match_mp_tac letrec_lemma >>
                     imp_res_tac infer_e_wfs >>
                     imp_res_tac pure_add_constraints_apply >>
                     `LENGTH funs = LENGTH funs_ts` by metis_tac [LENGTH_COUNT_LIST] >>
                     fs [GSYM MAP_MAP_o, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP] >>
                     metis_tac [MAP_MAP_o, combinTheory.o_DEF, sub_completion_apply_list]) >>
     rw [],
 metis_tac [sub_completion_infer_es],
 metis_tac [infer_e_wfs, infer_e_next_uvar_mono, check_env_more],
 rw [type_pes_def, RES_FORALL],
 `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `∃ts. sub_completion (num_tvs tenv) (st'''' with subst:= s'').next_uvar (st'''' with subst:= s'').subst ts s` 
                   by metis_tac [sub_completion_infer_pes] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv) st''''.next_uvar st''''.subst ts s` 
              by metis_tac [sub_completion_unify2] >>
     `∃ts. sub_completion (num_tvs tenv) (st'' with subst := s').next_uvar (st'' with subst := s').subst ts s` 
              by metis_tac [sub_completion_infer] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv) st''.next_uvar st''.subst ts s` 
              by metis_tac [sub_completion_unify2] >>
     `type_p (num_tvs tenv) cenv p (convert_t (t_walkstar s t)) (convert_env s env')`
              by metis_tac [infer_p_sound] >>
     `t_wfs (st'' with subst := s').subst`
           by (rw [] >>
               metis_tac [infer_p_wfs, t_unify_wfs]) >>
     imp_res_tac infer_p_check_t >>
     `check_env (count (st'' with subst:=s').next_uvar) (merge (MAP (λ(n,t). (n,0,t)) (SND (t,env'))) env)`
           by (rw [check_env_merge] >|
               [rw [check_env_def, EVERY_MAP, remove_pair_lem] >>
                    fs [EVERY_MEM] >>
                    rw [] >>
                    PairCases_on `x` >>
                    fs [] >>
                    res_tac >>
                    fs [],
                metis_tac [infer_p_next_uvar_mono, check_env_more]]) >>
     `tenv_inv s (merge (MAP (λ(n,t). (n,0,t)) env') env) (bind_var_list 0 (convert_env s env') tenv)` 
              by (metis_tac [tenv_inv_merge]) >>
     `type_e (convert_menv menv) cenv (bind_var_list 0 (convert_env s env') tenv) e (convert_t (t_walkstar s t2'))`
               by metis_tac [check_env_merge, SND, num_tvs_bind_var_list] >>
     rw [type_pes_cons] >|
     [imp_res_tac infer_p_bindings >>
          metis_tac [APPEND_NIL],
      qexists_tac `(convert_env s env')` >>
           rw [] >>
           imp_res_tac infer_p_wfs >>
           imp_res_tac infer_e_wfs >>
           imp_res_tac t_unify_apply >>
           metis_tac [t_unify_wfs, sub_completion_apply],
      `t_wfs (st'''' with subst := s'').subst`
           by (rw [] >>
               metis_tac [t_unify_wfs, infer_e_wfs]) >>
          `(st.next_uvar ≤ (st'''' with subst := s'').next_uvar)` 
                  by (fs [] >>
                      imp_res_tac infer_p_next_uvar_mono >>
                      imp_res_tac infer_e_next_uvar_mono >>
                      fs [] >>
                      decide_tac) >>
          `check_env (count (st'''' with subst := s'').next_uvar) env` by metis_tac [check_env_more] >>
          metis_tac []],
 `t_wfs st'''.subst ∧ t_wfs (st with next_uvar := st.next_uvar + 1).subst` by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     imp_res_tac sub_completion_infer_funs >>
     `tenv_inv s ((x,0,Infer_Tuvar st.next_uvar)::env) (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv)`
              by (match_mp_tac tenv_inv_extend0 >>
                  rw []) >>
     `num_tvs (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv) = num_tvs tenv`
              by fs [num_tvs_def, bind_tenv_def] >>
     `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) env ∧
      check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                by (rw [check_t_def] >>
                    metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
     `type_e (convert_menv menv) cenv (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv)
             e (convert_t (t_walkstar s t))`
                 by metis_tac [] >>
     `check_env (count st'''.next_uvar) env`
                 by (metis_tac [check_env_more, infer_e_next_uvar_mono]) >>
     `type_funs (convert_menv menv) cenv tenv funs (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs ts')`
               by metis_tac [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >|
     [rw [check_freevars_def] >>
          match_mp_tac check_t_to_check_freevars >>
          rw [] >>
          fs [sub_completion_def] >|
          [`st.next_uvar < st'''.next_uvar`
                    by (imp_res_tac infer_e_next_uvar_mono >>
                        fs [] >>
                        decide_tac) >>
               `st.next_uvar ∈ FDOM s`
                    by fs [count_def, SUBSET_DEF] >>
               metis_tac [],
           match_mp_tac (hd (CONJUNCTS check_t_walkstar)) >>
               rw [] >>
               `check_t 0 (count (st'''.next_uvar)) t`
                         by (imp_res_tac infer_e_check_t >>
                             fs [GSYM bind_def, check_env_bind]) >>
               metis_tac [check_t_more5]],
      imp_res_tac infer_funs_length >>
          rw [lookup_notin, MAP2_MAP, LENGTH_MAP2, MAP_MAP_o, combinTheory.o_DEF, map_zip_lem]]]);

val tenv_inv_merge2 = Q.prove (
`!env tenv env'' s tvs.
  tenv_inv FEMPTY env tenv 
  ⇒
  tenv_inv FEMPTY
    (merge (MAP (λx. (FST x,tvs,t_walkstar s (SND x))) env'') env)
    (bind_var_list2 (MAP (λx. (FST x,tvs, convert_t (t_walkstar s (SND x)))) env'') tenv)`,
induct_on `env''` >>
rw [bind_var_list2_def, merge_def] >>
PairCases_on `h` >>
rw [bind_var_list2_def, merge_def] >>
res_tac >>
fs [merge_def, tenv_inv_def, bind_tenv_def, lookup_tenv_def] >>
rw [deBruijn_inc0, t_walkstar_FEMPTY] >>
metis_tac [t_walkstar_FEMPTY]);

val letrec_lemma2 = Q.prove (
`!funs_ts l l' s s'.
 (!t1 t2. t_walkstar s t1 = t_walkstar s t2 ⇒  t_walkstar s' t1 = t_walkstar s' t2) ∧
 (LENGTH funs_ts = LENGTH l) ∧
 (LENGTH funs_ts = LENGTH l') ∧
 MAP (λn. t_walkstar s (Infer_Tuvar n)) l' = MAP (t_walkstar s) funs_ts
 ⇒
 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar s' (Infer_Tuvar n))) l')
  =
  MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s' t))) l funs_ts)`,
induct_on `funs_ts` >>
cases_on `l` >>
cases_on `l'` >>
rw [] >>
fs [] >|
[PairCases_on `h` >>
     rw [] >>
     metis_tac [],
 metis_tac []]);

val tenv_inv_merge3 = Q.prove (
`!l l' env tenv s tvs.
(LENGTH l = LENGTH l') ∧
tenv_inv FEMPTY env tenv
⇒
tenv_inv FEMPTY
  (merge
     (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
        (MAP (λx. t_walkstar s (Infer_Tuvar x))
           l')) env)
  (bind_var_list2
     (MAP (λ(x,tvs,t). (x,tvs,convert_t t))
        (MAP2 (λ(f,x,e) t. (f,tvs,t)) l
           (MAP (λx. t_walkstar s (Infer_Tuvar x))
              l'))) tenv)`,
induct_on `l` >>
rw [] >>
cases_on `l'` >>
rw [merge_def, bind_var_list2_def] >>
fs [] >>
PairCases_on `h` >>
fs [merge_def, bind_var_list2_def] >>
fs [merge_def, tenv_inv_def, bind_tenv_def, lookup_tenv_def] >>
rw [deBruijn_inc0, t_walkstar_FEMPTY] >>
fs [t_walkstar_FEMPTY] >>
res_tac >>
metis_tac []);

val helper_lemma = Q.prove (
`!l1 l2 n.
  (LENGTH l1 = LENGTH l2) ∧
  check_env (count n) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l1 (MAP (λn. Infer_Tuvar n) l2))
  ⇒
  check_env (count (SUC n)) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l1 (MAP (λn. Infer_Tuvar n) (MAP SUC l2)))`,
induct_on `l1` >>
rw [] >>
Cases_on `l2` >>
fs [check_env_def] >>
PairCases_on `h` >>
fs [check_t_def]);

val check_env_letrec = Q.prove (
`!l tvs.
  check_env (count (LENGTH l)) (MAP2 (λ(f,x,e) uvar. (f,tvs,uvar)) l (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`,
induct_on `l` >>
rw [COUNT_LIST_def] >>
rw [COUNT_LIST_def, check_env_def] >|
[PairCases_on `h` >>
     rw [check_t_def],
 fs [GSYM check_env_def] >>
     fs [MAP2_MAP, COUNT_LIST_def] >>
     metis_tac [helper_lemma, LENGTH_COUNT_LIST]]);

val convert_env2_def = Define `
convert_env2 env = MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env`;

val tenv_inv_convert_env2 = Q.prove (
`!env. tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)`,
Induct >>
rw [convert_env2_def, bind_var_list2_def, tenv_inv_def] >>
PairCases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [t_walkstar_FEMPTY, deBruijn_inc0, lookup_tenv_def, bind_tenv_def, lookup_def, bind_var_list2_def] >>
fs [tenv_inv_def] >>
res_tac >>
fs [t_walkstar_FEMPTY] >>
metis_tac [convert_env2_def]);

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

val oc_tvar_db = Q.prove (
`!s uv tvs. t_wfs s ⇒ ~t_oc s (Infer_Tvar_db tvs) uv`,
rw [] >>
imp_res_tac t_oc_eqn >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum (ASSUME_TAC o Q.SPECL [`uv`, `Infer_Tvar_db tvs`]) >>
rw [t_walk_eqn]);

val oc_unit = Q.prove (
`!s uv tc. t_wfs s ⇒ ~t_oc s (Infer_Tapp [] tc) uv`,
rw [] >>
imp_res_tac t_oc_eqn >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum (ASSUME_TAC o Q.SPECL [`uv`, `Infer_Tapp [] tc'`]) >>
rw [t_walk_eqn]);

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

val mem_to_flookup = Q.prove (
`!x y l. ALL_DISTINCT (MAP FST l) ∧ MEM (x,y) l ⇒ (FLOOKUP (FEMPTY |++ l) x = SOME y)`,
induct_on `l` >>
rw [lookup_append, flookup_update_list_some] >|
[full_case_tac >>
     rw [] >>
     imp_res_tac lookup_in2 >>
     fs [MEM_MAP],
 full_case_tac >>
     rw [] >>
     fs [flookup_update_list_some] >|
     [imp_res_tac lookup_notin >>
          fs [MEM_MAP] >>
          metis_tac [FST],
      metis_tac [optionTheory.SOME_11]]]);

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
cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') t` >>
rw [] >>
fs [flookup_update_list_none, flookup_update_list_some, infer_subst_var_def] >>
cases_on `FLOOKUP (FEMPTY |++ s') t` >>
rw [] >>
fs [flookup_update_list_none, flookup_update_list_some, infer_subst_var_def] >>
imp_res_tac lookup_notin >>
imp_res_tac lookup_in2 >>
fs [MEM_MAP] >|
[PairCases_on `y` >>
     fs [LAMBDA_PROD, GSYM PFORALL_THM] >>
     metis_tac [],
 PairCases_on `y'` >>
     fs [LAMBDA_PROD, GSYM PFORALL_THM] >>
     metis_tac [],
 PairCases_on `y''` >>
     fs [LAMBDA_PROD, GSYM PFORALL_THM] >>
     rw [] >>
     `FLOOKUP s (FST y) = NONE`
               by (fs [DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, map_fst, MEM_MAP] >>
                   `FST y ∉ FDOM s` by metis_tac [] >>
                   rw [FLOOKUP_DEF]) >>
     rw [infer_subst_var_def] >>
     imp_res_tac mem_to_flookup >>
     rw [] >>
     `lookup (FST y) (REVERSE (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s')) = SOME (Infer_Tvar_db x')`
              by metis_tac [lookup_map, MAP_REVERSE] >>
     fs [] >>
     rw [] >>
     fs [flookup_update_list_some],
 cases_on `x` >>
     rw [infer_subst_var_def],
 cases_on `x` >>
     rw [infer_subst_var_def]]);
 

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
fs [t_walk_eqn] >|
[induct_on `l` >>
     rw [],
 `infer_subst_var (FEMPTY |++ s') (t_vwalk s n) = t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n`
          by metis_tac [generalise_complete_lemma4] >>
     cases_on `t_vwalk s n` >>
     rw [] >>
     cases_on `t_vwalk (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) s') n` >>
     rw [] >> 
     fs [infer_subst_def, infer_subst_var_def] >>
     rw [MAP_MAP_o, MAP_EQ_f] >>
     cases_on `FLOOKUP (FEMPTY |++ s') n'` >>
     fs [flookup_update_list_none, flookup_update_list_some]]);

val generalise_complete_lemma6 = Q.prove (
`!e l f.
  MEM e l ∧ set (MAP f l) = {{}} 
  ⇒
  (f e = {})`,
induct_on `l` >>
rw [] >>
fs [MEM_MAP, EXTENSION] >>
metis_tac []);

val fst_lem = Q.prove (
`FST = (\(x,y).x)`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
rw []);

val no_vars_extend_subst_vwalk = Q.prove (
`!s. t_wfs s ⇒
   !n s'. t_wfs (s |++ s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
         (!n'. t_vwalk s n ≠ Infer_Tuvar n')
         ⇒
         t_vwalk (s |++ s') n = t_vwalk s n`,
strip_tac >>
strip_tac >>
imp_res_tac (DISCH_ALL t_vwalk_ind) >>
pop_assum ho_match_mp_tac >>
rw [] >>
pop_assum mp_tac >>
imp_res_tac t_vwalk_eqn >>
ONCE_ASM_REWRITE_TAC [] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
cases_on `FLOOKUP (s |++ s') n` >>
rw [] >>
fs [flookup_update_list_none, flookup_update_list_some, infer_subst_var_def] >>
cases_on `FLOOKUP s n` >>
fs [t_vars_eqn] >|
[fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF, FDOM_FUPDATE_LIST] >>
     imp_res_tac lookup_in2 >>
     fs [MEM_MAP] >>
     metis_tac [],
 cases_on `x` >>
     fs [] >>
     rw [] >>
     fs [] >>
     metis_tac [t_vwalk_eqn]]);

val no_vars_extend_subst = Q.prove (
`!s. t_wfs s ⇒
  !t s'. t_wfs (s |++ s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
         (t_vars (t_walkstar s t) = {})
         ⇒
         t_walkstar (s |++ s') t = t_walkstar s t`,
strip_tac >>
strip_tac >>
imp_res_tac t_walkstar_ind >>
pop_assum ho_match_mp_tac >>
rw [] >>
cases_on `t` >>
rw [t_walkstar_eqn, t_walk_eqn, infer_subst_def] >>
fs [t_walk_eqn] >>
pop_assum mp_tac >>
rw [t_walkstar_eqn, t_walk_eqn, t_vars_eqn] >>
rw [MAP_EQ_f] >-
metis_tac [generalise_complete_lemma6, MAP_MAP_o, combinTheory.o_DEF] >>
cases_on `t_vwalk s n` >>
fs [] >>
rw [no_vars_extend_subst_vwalk] >>
rw [MAP_EQ_f] >>
fs [t_vars_eqn] >>
rw [] >>
fs [] >>
metis_tac [generalise_complete_lemma6, MAP_MAP_o, combinTheory.o_DEF]);

val generalise_complete = Q.prove (
`!s l tvs s' ts tvs next_uvar.
  t_wfs s ∧
  check_s 0 (count next_uvar) s ∧
  EVERY (\t. check_t 0 (count next_uvar) t) l ∧
  (generalise_list 0 0 FEMPTY (MAP (t_walkstar s) l) = (tvs,s',ts))
  ⇒
  ?ec1 last_sub. 
    (ts = MAP (t_walkstar last_sub) l) ∧
    t_wfs last_sub ∧
    sub_completion tvs next_uvar s ec1 last_sub`,
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
                 cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts) x'` >>
                 rw [flookup_update_list_some, flookup_update_list_none] >-
                 fs [flookup_update_list_none] >>
                 pop_assum mp_tac >>
                 rw [flookup_update_list_some] >>
                 rw [] >>
                 imp_res_tac lookup_in2 >>
                 pop_assum mp_tac >>
                 rw [MEM_MAP, MAP_REVERSE] >>
                 PairCases_on `y'` >>
                 rw [] >>
                 `MEM y'0 (MAP FST ts)` by (rw [MEM_MAP] >> metis_tac [FST]) >>
                 `y'0 ∈ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                 `y'0 ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                 `FLOOKUP s y'0 = NONE` by metis_tac [FLOOKUP_DEF] >>
                 rw [] >>
                 fs [] >>
                 `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) y'0 = SOME x''` by rw [flookup_update_list_some] >>
                 imp_res_tac lookup_in >>
                 fs [MEM_MAP] >>
                 rw [] >>
                 PairCases_on `y''` >>
                 rw [] >>
                 rw [t_vars_eqn, encode_infer_t_def]) >>
         fs [t_vars_eqn, t_wfs_eqn] >>
         metis_tac []) >>
`t_wfs (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)` 
      by (`t_vR s = t_vR (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2)`
             by (rw [t_vR_eqn, FUN_EQ_THM] >>
                 cases_on `FLOOKUP (s |++ MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts |++ ts2) x'` >>
                 rw [flookup_update_list_some, flookup_update_list_none] >-
                 fs [flookup_update_list_none] >>
                 pop_assum mp_tac >>
                 rw [flookup_update_list_some] >|
                 [imp_res_tac lookup_in2 >>
                      pop_assum mp_tac >>
                      rw [MAP_REVERSE] >>
                      `x' ∈ FDOM (FEMPTY |++ ts2)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                      `x' ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s x' = NONE` by metis_tac [FLOOKUP_DEF] >>
                      rw [] >>
                      `FLOOKUP (FEMPTY |++ ts2) x' = SOME x''` by rw [flookup_update_list_some] >>
                      pop_assum mp_tac >>
                      rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                      rw [encode_infer_t_def],
                 imp_res_tac lookup_in2 >>
                      pop_assum mp_tac >>
                      rw [MEM_MAP, MAP_REVERSE] >>
                      PairCases_on `y'` >>
                      rw [] >>
                      `MEM y'0 (MAP FST ts)` by (rw [MEM_MAP] >> metis_tac [FST]) >>
                      `y'0 ∈ FDOM (FEMPTY |++ ts)` by metis_tac [FDOM_FUPDATE_LIST, IN_UNION] >>
                      `y'0 ∉ FDOM s` by (fs [DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
                      `FLOOKUP s y'0 = NONE` by metis_tac [FLOOKUP_DEF] >>
                      rw [] >>
                      fs [] >>
                      `FLOOKUP (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) y'0 = SOME x''` by rw [flookup_update_list_some] >>
                      imp_res_tac lookup_in >>
                      fs [MEM_MAP] >>
                      rw [] >>
                      PairCases_on `y''` >>
                      rw [] >>
                      rw [t_vars_eqn, encode_infer_t_def],
                  rw []]) >>
         fs [t_vars_eqn, t_wfs_eqn] >>
         metis_tac []) >>
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
             by metis_tac [generalise_complete_lemma6, MAP_MAP_o] >>
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
                    by (rw [flookup_update_list_some] >>
                        metis_tac [lookup_all_distinct, MEM_REVERSE, ALL_DISTINCT_REVERSE, REVERSE_REVERSE, MAP_REVERSE]) >>
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
          `(!uv. uv ∈ FDOM (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ⇒ ∃tv. (FEMPTY |++ (MAP (λ(uv,tv). (uv,Infer_Tvar_db tv)) ts)) ' uv = Infer_Tvar_db tv ∧ tv < tvs)`
                   by metis_tac [generalise_complete_lemma] >>
          fs [FLOOKUP_DEF] >>
          metis_tac [check_t_def],
      fs [check_s_def, FLOOKUP_DEF] >>
          metis_tac [check_t_more2, check_t_more5, arithmeticTheory.ADD_0]]]);

val check_build_ctor_tenv = Q.prove (
`!mn cenv l. check_ctor_tenv mn cenv l ⇒ check_cenv (build_ctor_tenv mn l)`,
induct_on `l` >>
rw [check_cenv_def, build_ctor_tenv_def, check_ctor_tenv_def] >|
[PairCases_on `h` >>
     rw [EVERY_MAP] >>
     fs [remove_pair_lem] >>
     fs [every_shim, EVERY_MAP],
 fs [check_cenv_def, build_ctor_tenv_def, check_ctor_tenv_def] >>
     `check_dup_ctors mn cenv l` 
                by (PairCases_on `h` >> metis_tac [check_dup_ctors_cons]) >>
     metis_tac []]);

val infer_d_check_helper = Q.prove (
`!l1 l2 s tvs.
  (LENGTH l1 = LENGTH l2) ∧
  EVERY (\n. check_t tvs {} (t_walkstar s (Infer_Tuvar n))) l2
  ⇒
  EVERY (λx. (λ(x,tvs,t). check_t tvs ∅ t) ((λ((f,x,e),t). (f,tvs,t)) x))
    (ZIP (l1, MAP (t_walkstar s) (MAP (λn. Infer_Tuvar n) l2)))`,
Induct_on `l2` >>
rw [COUNT_LIST_def, EVERY_MAP] >>
cases_on `l1` >>
fs [] >>
PairCases_on `h'` >>
rw []);

val infer_d_check_s_helper1 = Q.prove (
`!menv cenv env e t1 st1 p t env2 st2 s.
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env ∧
  (infer_e menv cenv env e init_infer_state = (Success t1, st1)) ∧
  (infer_p cenv p st1 = (Success (t, env2), st2)) ∧
  (t_unify st2.subst t1 t = SOME s)
  ⇒
  check_s 0 (count st2.next_uvar) s`,
rw [] >>
fs [success_eqns, init_state_def] >>
`t_wfs init_infer_state.subst ∧ 
 ((count (init_infer_state:(num|->infer_t) infer_st).next_uvar) = {}) ∧
 check_s 0 (count init_infer_state.next_uvar) init_infer_state.subst`
           by (fs [init_infer_state_def] >>
               rw [t_wfs_def, check_s_def]) >>
`t_wfs st1.subst ∧ t_wfs st2.subst` by metis_tac [infer_p_wfs, infer_e_wfs] >>
`check_t 0 (count st2.next_uvar) t1 ∧
 check_t 0 (count st2.next_uvar) t`
            by metis_tac [infer_p_check_t, infer_e_check_t,
                          check_t_more4, infer_p_next_uvar_mono] >>
 match_mp_tac t_unify_check_s >>
 prove_tac [infer_p_check_s, infer_e_check_s]);

val infer_d_check_s_helper2 = Q.prove (
`!menv cenv l env funs_ts st1 st2 s.
    (LENGTH funs_ts = LENGTH l) ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env {} env ∧
    infer_funs menv cenv
        (merge
           (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l
              (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))) env) l
        (init_infer_state with next_uvar := LENGTH l) = (Success funs_ts,st2) ∧
     pure_add_constraints st2.subst
        (ZIP (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)),funs_ts))
        s
 ⇒
 check_s 0 (count st2.next_uvar) s`,
rw [] >>
fs [success_eqns, init_state_def] >>
match_mp_tac pure_add_constraints_check_s >>
`check_env (count (LENGTH l))
        (merge
           (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l
              (MAP (λn. Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l)))) env)`
         by (rw [check_env_merge, check_env_letrec_lem] >>
             metis_tac [check_env_more, COUNT_ZERO, DECIDE ``!x. 0 ≤ x:num``]) >>
`t_wfs init_infer_state.subst ∧ check_s 0 {} init_infer_state.subst` by fs [check_s_def, t_wfs_def, init_infer_state_def] >>
`check_s 0 (count (init_infer_state with next_uvar := LENGTH l).next_uvar) (init_infer_state with next_uvar := LENGTH l).subst`
          by (fs [] >> metis_tac [check_s_more2, infer_e_wfs, COUNT_ZERO, DECIDE ``!x. 0 ≤ x:num``]) >>
qexists_tac `st2.subst` >>
qexists_tac `(ZIP (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)),funs_ts))` >>
rw [] >|
[`t_wfs (init_infer_state with next_uvar := LENGTH l).subst` by rw [] >>
     metis_tac [infer_e_wfs],
 rw [EVERY_CONJ, every_shim2, every_zip_snd, every_zip_fst, LENGTH_COUNT_LIST, EVERY_MAP,
     every_count_list, check_t_def] >>
     `(init_infer_state with next_uvar := LENGTH l).next_uvar ≤ st2.next_uvar` by metis_tac [infer_e_next_uvar_mono] >|
     [fs [] >>
          decide_tac,
      imp_res_tac infer_e_check_t >>
          fs [] >>
          metis_tac [check_env_more]],
 match_mp_tac (hd (tl(tl(tl(CONJUNCTS infer_e_check_s))))) >>
     MAP_EVERY qexists_tac [`menv`, `cenv`, 
                            `(merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l (MAP (λn. Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l)))) env)`,
                            `l`,
                            `(init_infer_state with next_uvar := LENGTH l)`,
                            `funs_ts`] >>
     rw [] >>
     fs []]);

val infer_d_check = Q.prove (
`!mn menv cenv env d st1 st2 cenv' env' tenv.
  infer_d mn menv cenv env d st1 = (Success (cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  check_cenv cenv' ∧
  check_env {} env'`,
cases_on `d` >>
REPEAT GEN_TAC >>
STRIP_TAC >>
fs [infer_d_def, success_eqns] >>
fs [emp_def] >|
[`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     fs [success_eqns] >>
     `?tvs s ts. generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env'')) = (tvs,s,ts)`
                 by (cases_on `generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env''))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [METIS_PROVE [] ``!x. (x = 0:num ∨ is_value e) = (x<>0 ⇒ is_value e)``] >>
     rw [] >>
     fs [success_eqns] >>
     rw [check_cenv_def, check_env_def] >>
     `st''.next_uvar = 0` by (fs [init_state_def, init_infer_state_def] >> rw []) >>
     fs [] >>
     imp_res_tac infer_p_check_t >>
     fs [every_shim, init_state_def] >>
     `t_wfs init_infer_state.subst` by rw [t_wfs_def, init_infer_state_def] >>
     `t_wfs s` by metis_tac [t_unify_wfs, infer_e_wfs, infer_p_wfs] >>
     `?ec1 last_sub.
       (ts = MAP (t_walkstar last_sub) (MAP SND env'')) ∧
       t_wfs last_sub ∧
       sub_completion tvs st''''.next_uvar s ec1 last_sub`
                  by metis_tac [generalise_complete, infer_d_check_s_helper1] >>
     rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP] >>
     fs [EVERY_MAP] >>
     fs [sub_completion_def] >>
     fs [EVERY_MEM] >>
     rw [] >>
     res_tac >>
     match_mp_tac (hd (CONJUNCTS check_t_walkstar)) >>
     metis_tac [check_t_more5],
 fs [success_eqns] >>
     `?tvs s ts. generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l)))) = (tvs,s,ts)`
                 by (cases_on `generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l))))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [success_eqns] >>
     rw [] >>
     fs [success_eqns] >>
     rw [check_cenv_def] >>
     `EVERY (\t. check_t 0 (count st''''.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))`
                 by (rw [EVERY_MAP, check_t_def] >>
                     rw [EVERY_MEM, MEM_COUNT_LIST] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     decide_tac) >>
     `st'''.next_uvar = 0` by (fs [init_state_def, init_infer_state_def] >> rw []) >>
     fs [init_state_def] >>
     `t_wfs (st''' with next_uvar := LENGTH l).subst` by rw [t_wfs_def, init_infer_state_def] >>
     `t_wfs st'''''.subst` by metis_tac [infer_e_wfs, pure_add_constraints_wfs] >>
     `?ec1 last_sub. 
        (ts = MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))) ∧
        t_wfs last_sub ∧
        sub_completion tvs st''''.next_uvar st'''''.subst ec1 last_sub`
                 by metis_tac [generalise_complete, infer_d_check_s_helper2, LENGTH_COUNT_LIST] >>
     rw [] >>
     fs [sub_completion_def] >>
     `LENGTH l = LENGTH (MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`
             by metis_tac [LENGTH_COUNT_LIST, LENGTH_MAP] >>
     rw [check_env_def, MAP2_ZIP, EVERY_MAP] >>
     match_mp_tac infer_d_check_helper >>
     rw [LENGTH_COUNT_LIST] >>
     fs [LENGTH_COUNT_LIST, every_count_list] >>
     rw [] >>
     imp_res_tac infer_e_next_uvar_mono >>
     fs [] >>
     `n < st''''.next_uvar` by decide_tac >>
     `n ∈ FDOM last_sub` by fs [SUBSET_DEF] >>
     metis_tac [],
 every_case_tac >>
     fs [success_eqns] >>
     rw [check_env_def] >>
     metis_tac [check_build_ctor_tenv],
 every_case_tac >>
     fs [success_eqns] >>
     rw [] >>
     fs [check_env_def, check_cenv_def, bind_def]]);

val infer_d_sound = Q.prove (
`!mn menv cenv env d st1 st2 cenv' env' tenv.
  infer_d mn menv cenv env d st1 = (Success (cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  type_d mn (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) d cenv' (convert_env2 env')`,
cases_on `d` >>
REPEAT GEN_TAC >>
STRIP_TAC >>
fs [infer_d_def, success_eqns, type_d_cases] >>
fs [emp_def] >|
[`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     fs [success_eqns] >>
     `?tvs s ts. generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env'')) = (tvs,s,ts)`
                 by (cases_on `generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env''))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [METIS_PROVE [] ``!x. (x = 0:num ∨ is_value e) = (x<>0 ⇒ is_value e)``] >>
     rw [] >>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv' = bind_tvar tvs (bind_var_list2 (convert_env2 env) Empty)` >>
     fs [init_state_def] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     `init_infer_state.next_uvar = 0` 
                 by (fs [init_infer_state_def] >> rw []) >>
     `check_t 0 (count st'''.next_uvar) t1` by metis_tac [infer_e_check_t, COUNT_ZERO] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     fs [] >>
     rw [] >>
     fs [] >>
     imp_res_tac infer_p_check_t >>
     fs [every_shim] >>
     `t_wfs s` by metis_tac [t_unify_wfs, infer_p_wfs] >>
     `?last_sub ec1. sub_completion tvs st''''.next_uvar s ec1 last_sub ∧
                     t_wfs last_sub ∧
                     (ts = MAP (t_walkstar last_sub) (MAP SND env''))`
                          by metis_tac [generalise_complete, infer_d_check_s_helper1] >>
     `num_tvs tenv' = tvs` 
                  by (Q.UNABBREV_TAC `tenv'` >>
                      fs [bind_tvar_def] >> 
                      full_case_tac >>
                      rw [num_tvs_def, num_tvs_bvl2]) >>
     imp_res_tac sub_completion_unify2 >>
     `?ec2. sub_completion (num_tvs tenv') st'''.next_uvar st'''.subst (ec2++((t1,t)::ec1)) last_sub` 
               by metis_tac [sub_completion_infer_p] >>
     rw [] >>
     `(init_infer_state:(num |-> infer_t) infer_st).subst = FEMPTY` by fs [init_infer_state_def] >>
     `tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)` by metis_tac [tenv_inv_convert_env2] >>
     `tenv_inv FEMPTY env tenv'` by metis_tac [tenv_inv_extend_tvar_empty_subst] >>
     `tenv_inv last_sub env tenv'` by metis_tac [tenv_inv_empty_to] >>
     `type_e (convert_menv menv) cenv tenv' e (convert_t (t_walkstar last_sub t1))`
             by metis_tac [infer_e_sound, COUNT_ZERO] >>
     `type_p (num_tvs tenv') cenv p (convert_t (t_walkstar last_sub t)) (convert_env last_sub env'')`
             by metis_tac [infer_p_sound] >>
     `t_walkstar last_sub t = t_walkstar last_sub t1`
             by (imp_res_tac infer_e_wfs >>
                 imp_res_tac infer_p_wfs >>
                 imp_res_tac t_unify_wfs >>
                 metis_tac [sub_completion_apply, t_unify_apply]) >>
     cases_on `num_tvs tenv' = 0` >>
     rw [] >|
     [disj2_tac >>
          qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env'')` >>
          rw [] >|
          [rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
               REPEAT (pop_assum (fn _ => all_tac)) >> 
               induct_on `env''` >>
               rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
               (PairCases_on `h` >>
                    rw []) >>
               rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem],
           imp_res_tac infer_p_bindings >>
               fs [],
           metis_tac [],
           fs [bind_tvar_def]],
      disj1_tac >>
          qexists_tac `num_tvs tenv'` >>
          qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env'')` >>
          rw [] >|
          [rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
               REPEAT (pop_assum (fn _ => all_tac)) >> 
               induct_on `env''` >>
               rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
               (PairCases_on `h` >>
                    rw []) >>
               rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem],
           imp_res_tac infer_p_bindings >>
               fs []]],
 fs [success_eqns] >>
     `?tvs s ts. generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l)))) = (tvs,s,ts)`
                 by (cases_on `generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l))))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [] >>
     rw [] >>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv' = bind_tvar tvs (bind_var_list2 (convert_env2 env) Empty)` >>
     fs [init_state_def] >>
     rw [] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     `init_infer_state.next_uvar = 0` 
                 by (fs [init_infer_state_def] >> rw []) >>
     fs [] >>
     rw [] >>
     fs [] >>
     `EVERY (\t. check_t 0 (count st''''.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))`
                 by (rw [EVERY_MAP, check_t_def] >>
                     rw [EVERY_MEM, MEM_COUNT_LIST] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     decide_tac) >>
     `t_wfs st'''''.subst` by metis_tac [pure_add_constraints_wfs, infer_e_wfs, infer_st_rewrs] >>
     `?last_sub ec1. sub_completion tvs st''''.next_uvar st'''''.subst ec1 last_sub ∧
                     t_wfs last_sub ∧
                     (ts = MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`
                          by metis_tac [generalise_complete, infer_d_check_s_helper2, LENGTH_COUNT_LIST] >>
     imp_res_tac sub_completion_add_constraints >>
     rw [] >>
     `(init_infer_state:(num |-> infer_t) infer_st).subst = FEMPTY` by fs [init_infer_state_def] >>
     `tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)` by metis_tac [tenv_inv_convert_env2] >>
     `tenv_inv FEMPTY env tenv'` by metis_tac [tenv_inv_extend_tvar_empty_subst] >>
     `tenv_inv last_sub env tenv'` by metis_tac [tenv_inv_empty_to] >>
     Q.ABBREV_TAC `tenv'' = 
                   bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l)))) 
                                 tenv'` >> 
     Q.ABBREV_TAC `env'' = merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l (MAP (λn. Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l)))) env` >>
     `tenv_inv last_sub env'' tenv''` by metis_tac [tenv_inv_letrec_merge] >>
     fs [] >>
     `check_env (count (LENGTH l)) env''` 
                 by (Q.UNABBREV_TAC `env''` >>
                     rw [MAP2_MAP, check_env_merge, check_env_letrec] >>
                     metis_tac [check_env_more, COUNT_ZERO, DECIDE ``0<=x:num``]) >> 
     `num_tvs tenv'' = tvs`
                 by  (Q.UNABBREV_TAC `tenv''` >>
                      rw [num_tvs_bind_var_list] >>
                      Q.UNABBREV_TAC `tenv'` >>
                      fs [bind_tvar_rewrites, num_tvs_bvl2, num_tvs_def]) >>
     `type_funs (convert_menv menv) cenv tenv'' l (MAP2 (λ(x,y,z) t. (x,(convert_t o t_walkstar last_sub) t)) l funs_ts)`
             by (match_mp_tac (List.nth (CONJUNCTS infer_e_sound, 3)) >>
                 rw [] >>
                 qexists_tac `env''` >>
                 qexists_tac `init_infer_state with next_uvar := LENGTH l` >>
                 rw [] >>
                 metis_tac [num_tvs_bind_var_list]) >>
     `t_wfs (init_infer_state with next_uvar := LENGTH l).subst` by rw [] >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     qexists_tac `(MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l))))` >>
     qexists_tac `tvs` >>
     rw [] >|
     [rw [LENGTH_MAP, LENGTH_COUNT_LIST, MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
          REPEAT (pop_assum (fn _ => all_tac)) >> 
          induct_on `l` >>
          rw [COUNT_LIST_def, tenv_add_tvs_def, convert_env_def, convert_env2_def] >-
          (PairCases_on `h` >> rw []) >>
          rw [MAP_MAP_o, MAP2_MAP, ZIP_MAP, LENGTH_COUNT_LIST, combinTheory.o_DEF, remove_pair_lem],
      `LENGTH l = LENGTH funs_ts` by fs [LENGTH_COUNT_LIST] >>
          fs [MAP_ZIP, LENGTH_COUNT_LIST, MAP_MAP_o, combinTheory.o_DEF] >>
          metis_tac [letrec_lemma2, LENGTH_COUNT_LIST, LENGTH_MAP, 
                     pure_add_constraints_wfs, sub_completion_apply]],
 full_case_tac >>
     fs [success_eqns] >>
     rw [convert_env2_def, bind_var_list2_def, merge_def],
 full_case_tac >>
     fs [success_eqns] >>
     rw [convert_env2_def]]);

val infer_ds_sound = Q.prove (
`!mn menv cenv env ds st1 cenv' env' st2 tenv.
  infer_ds mn menv cenv env ds st1 = (Success (cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  type_ds mn (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) ds cenv' (convert_env2 env')`,
induct_on `ds` >>
rw [infer_ds_def, success_eqns] >|
[rw [convert_env2_def, Once type_ds_cases, emp_def],
 PairCases_on `v'` >>
     fs [success_eqns] >>
     PairCases_on `v'` >>
     fs [success_eqns] >>
     rw [Once type_ds_cases] >>
     fs [init_infer_state_def] >>
     imp_res_tac infer_d_check >>
     `check_cenv (v'0 ++ cenv)` by fs [check_cenv_def] >>
     `check_env {} (v'1 ++ env)` 
                     by fs [check_env_def, init_infer_state_def] >>
     imp_res_tac infer_d_sound >>
     res_tac >>
     fs [convert_env2_def, merge_def, bvl2_append] >>
     metis_tac []]);

val infer_ds_check = Q.prove (
`!mn menv cenv env ds st1 st2 cenv' env' tenv.
  infer_ds mn menv cenv env ds st1 = (Success (cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  check_cenv cenv' ∧
  check_env {} env'`,
induct_on `ds` >>
rw [infer_ds_def, success_eqns] >|
[rw [check_cenv_def],
 rw [check_env_def],
 all_tac,
 all_tac] >>
PairCases_on `v'` >>
fs [success_eqns] >>
PairCases_on `v'` >>
fs [success_eqns] >>
rw [] >>
`check_env {} v'1 ∧ check_cenv v'0` by metis_tac [infer_d_check] >>
`check_env {} (v'1 ++ env) ∧ check_cenv (v'0 ++ cenv)` 
           by fs [check_env_def, check_cenv_def] >>
`check_env {} v'1' ∧ check_cenv v'0'` by metis_tac [] >>
fs [check_cenv_def, check_env_def]);

val check_t_infer_db_subst2 = Q.prove (
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
decide_tac >-
decide_tac >-
metis_tac []);

val t_walkstar_no_vars = Q.prove (
`!t tvs s. 
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (t_walkstar s t = t)`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw [] >>
metis_tac []);

val db_subst_infer_subst_swap2 = Q.prove (
`(!t s tvs uvar n.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
    (convert_t t))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  EVERY (\t. check_t tvs {} t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))) o
       convert_t)
      ts))`,
ho_match_mp_tac infer_t_induction >>
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST]);

val check_weakE_sound = Q.prove (
`!tenv1 tenv2 st st2.
  check_env {} tenv1 ∧
  check_env {} tenv2 ∧
  (check_weakE tenv1 tenv2 st = (Success (), st2))
  ⇒
  weakE (convert_env2 tenv1) (convert_env2 tenv2)`,
ho_match_mp_tac check_weakE_ind >>
rw [convert_env2_def, check_weakE_def, weakE_def, success_eqns, 
    SIMP_RULE (srw_ss()) [bind_def] check_env_bind] >>
cases_on `lookup n tenv1` >>
fs [success_eqns] >>
`?tvs_impl t_impl. x' = (tvs_impl,t_impl)` by (PairCases_on `x'` >> metis_tac []) >>
rw [] >>
fs [success_eqns] >>
rw [] >>
`lookup n (MAP (λ(x,y). (x,(λ(tvs,t). (tvs, convert_t t)) y)) tenv1) = SOME ((λ(tvs,t). (tvs, convert_t t)) (tvs_impl,t_impl))`
        by metis_tac [lookup_map] >>
fs [remove_pair_lem] >>
`(λ(x,y). (x,FST y,convert_t (SND y))) = (λ(x,tvs:num,t). (x,tvs,convert_t t))`
                by (rw [FUN_EQ_THM] >>
                    PairCases_on `y` >>
                    rw []) >>
rw [] >>
fs [init_state_def, init_infer_state_def] >>
rw [] >|
[fs [] >>
     `t_wfs FEMPTY` by rw [t_wfs_def] >>
     imp_res_tac t_unify_wfs >>
     imp_res_tac t_unify_apply >>
     imp_res_tac check_env_lookup >>
     `?s'. ALL_DISTINCT (MAP FST s') ∧ (FEMPTY |++ s' = FUN_FMAP (\x. Infer_Tapp [] TC_unit) (count tvs_impl DIFF FDOM s))`
                   by metis_tac [fmap_to_list] >>
     `FINITE (count tvs_impl DIFF FDOM s)` by metis_tac [FINITE_COUNT, FINITE_DIFF] >>
     `t_wfs (s |++ s')`
               by (`t_vR s = t_vR (s |++ s')`
                            by (rw [t_vR_eqn, FUN_EQ_THM] >>
                                cases_on `FLOOKUP (s |++ s') x'` >>
                                fs [flookup_update_list_none, flookup_update_list_some] >>
                                cases_on `FLOOKUP s x'` >>
                                fs [flookup_update_list_none, flookup_update_list_some] >>
                                `FLOOKUP (FEMPTY |++ s') x' = SOME x''` by rw [flookup_update_list_some] >>
                                pop_assum mp_tac >>
                                rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                                rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                                fs [FLOOKUP_DEF]) >>
                   fs [t_wfs_eqn]) >>
     `check_s tvs_spec (count tvs_impl) s`
                by (match_mp_tac t_unify_check_s >>
                    MAP_EVERY qexists_tac [`FEMPTY`, `t_spec`, 
                                           `(infer_deBruijn_subst (MAP (λn.  Infer_Tuvar n) (COUNT_LIST tvs_impl)) t_impl)`] >>
                    rw [check_s_def, check_t_infer_db_subst2] >>
                    metis_tac [check_t_more, check_t_more2, arithmeticTheory.ADD_0]) >>
     qexists_tac `MAP (\n. convert_t (t_walkstar (s |++ s') (Infer_Tuvar n))) (COUNT_LIST tvs_impl)` >>
     rw [LENGTH_COUNT_LIST, check_t_to_check_freevars, EVERY_MAP] >|
     [rw [EVERY_MEM] >>
          `FDOM (FEMPTY |++ s') = count tvs_impl DIFF FDOM s` by metis_tac [FDOM_FMAP] >>
          `check_t tvs_spec {} (t_walkstar (s |++ s') (Infer_Tuvar n'))`
                     by (rw [check_t_def] >>
                         match_mp_tac t_walkstar_check >>
                         rw [check_t_def, FDOM_FUPDATE_LIST] >|
                         [fs [check_s_def, fdom_fupdate_list2] >>
                              rw [] >>
                              rw [FUPDATE_LIST_APPLY_NOT_MEM] >>
                              `count tvs_impl ⊆ FDOM s ∪ set (MAP FST s')` by rw [SUBSET_DEF] >|
                              [metis_tac [check_t_more5],
                               metis_tac [check_t_more5],
                               `FLOOKUP (s |++ s') uv = SOME ((s |++ s') ' uv)`
                                           by (rw [FLOOKUP_DEF, FDOM_FUPDATE_LIST]) >>
                                   fs [flookup_update_list_some] >|
                                   [imp_res_tac lookup_in >>
                                        fs [MEM_MAP] >>
                                        rw [] >>
                                        PairCases_on `y` >>
                                        imp_res_tac mem_to_flookup >>
                                        pop_assum mp_tac >>
                                        rw [FLOOKUP_FUN_FMAP] >>
                                        rw [check_t_def],
                                    pop_assum mp_tac >>
                                        rw [FLOOKUP_DEF]]],
                          fs [EXTENSION, MEM_COUNT_LIST] >>
                              res_tac >>
                              fs [FDOM_FUPDATE_LIST]]) >>
          rw [check_t_to_check_freevars],
       imp_res_tac t_walkstar_no_vars >>
          fs [] >>
          rw [SIMP_RULE (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] (GSYM db_subst_infer_subst_swap2)] >>
          match_mp_tac (METIS_PROVE [] ``x = y ⇒ f x = f y``) >>
          match_mp_tac (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] no_vars_extend_subst) >>
          rw [] >|
          [rw [DISJOINT_DEF, EXTENSION] >>
               metis_tac [],
           imp_res_tac check_t_t_vars  >>
               fs [EXTENSION, SUBSET_DEF]]],
 metis_tac[]]);

val check_weakC_sound = Q.prove (
`!(tenvC1:tenvC) (tenvC2:tenvC).
  check_weakC tenvC1 tenvC2
  ⇒
  weakC tenvC1 tenvC2`,
induct_on `tenvC2` >>
fs [check_weakC_def, weakC_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [] >>
rw [] >>
cases_on `lookup cn tenvC1` >>
fs []);

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
rw [check_freevars_def] >>
metis_tac []);

val t_to_freevars_check = Q.prove (
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
metis_tac [check_freevars_more]);

val check_freevars_nub = Q.prove (
`(!t x fvs.
  check_freevars x fvs t ⇒
  check_freevars x (nub fvs) t) ∧
 (!ts x fvs.
  EVERY (check_freevars x fvs) ts ⇒
  EVERY (check_freevars x (nub fvs)) ts)`,
Induct >>
rw [check_freevars_def, GSYM nub_set] >>
metis_tac []);

val check_specs_sound = Q.prove (
`!mn cenv env specs st cenv' env' st'.
  (check_specs mn cenv env specs st = (Success (cenv',env'), st'))
  ⇒
  type_specs mn cenv (convert_env2 env) specs cenv' (convert_env2 env')`,
ho_match_mp_tac check_specs_ind >>
rw [check_specs_def, success_eqns] >|
[rw [Once type_specs_cases],
 rw [Once type_specs_cases] >>
     res_tac >>
     `check_freevars 0 fvs t` by metis_tac [t_to_freevars_check] >>
     `check_freevars 0 (nub fvs) t` by metis_tac [check_freevars_nub] >>
     qexists_tac `nub fvs` >>
     rw [] >>
     fs [LENGTH_MAP, convert_t_subst, bind_def, convert_env2_def, LENGTH_COUNT_LIST] >>
     fs [MAP_MAP_o, combinTheory.o_DEF, convert_t_def] >>
     metis_tac [],
 rw [Once type_specs_cases] >>
     metis_tac [],
 rw [Once type_specs_cases] >>
     fs [bind_def, emp_def] >>
     metis_tac [],
 rw [Once type_specs_cases] >|
     [fs [EVERY_MEM] >>
          rw [] >>
          PairCases_on `p` >>
          rw [] >>
          res_tac >>
          fs [],
      metis_tac []]]);

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
rw [check_t_def, infer_type_subst_def, EVERY_MAP] >>
every_case_tac >>
full_simp_tac (srw_ss()++ARITH_ss) [check_t_def, length_nub_append] >|
[imp_res_tac lookup_in2 >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     rw [] >>
     decide_tac,
 imp_res_tac lookup_in >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST, length_nub_append] >>
     rw [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def],
 imp_res_tac lookup_in >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST, length_nub_append] >>
     rw [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def]]);

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
rw [check_t_def, infer_type_subst_def, EVERY_MAP] >>
every_case_tac >>
full_simp_tac (srw_ss()++ARITH_ss) [check_t_def, nub_append] >|
[imp_res_tac lookup_in2 >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     rw [] >>
     decide_tac,
 imp_res_tac lookup_in >>
     `LENGTH (nub (FILTER (λx. x ∉ set fvs2) fvs1) ++ nub fvs2) =
      LENGTH (nub fvs2) + LENGTH (nub (FILTER (\x.x ∉ set fvs2) fvs1))`
              by metis_tac [LENGTH_APPEND, arithmeticTheory.ADD_COMM] >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     rw [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def],
 imp_res_tac lookup_in >>
     `LENGTH (nub (FILTER (λx. x ∉ set fvs2) fvs1) ++ nub fvs2) =
      LENGTH (nub fvs2) + LENGTH (nub (FILTER (\x.x ∉ set fvs2) fvs1))`
              by metis_tac [LENGTH_APPEND, arithmeticTheory.ADD_COMM] >>
     fs [MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST] >>
     rw [EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST, check_t_def]]);

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
rw [t_to_freevars_def, success_eqns, check_t_def, infer_type_subst_def] >>
rw [EVERY_MAP, nub_def, count_list_one, check_t_def] >>
metis_tac [check_lem, check_lem2]);

val check_specs_check = Q.prove (
`!mn cenv env specs st cenv' env' st'.
  check_cenv cenv ∧
  check_env {} env ∧
  (check_specs mn cenv env specs st = (Success (cenv',env'), st'))
  ⇒
  check_cenv cenv' ∧
  check_env {} env'`,
ho_match_mp_tac check_specs_ind >>
STRIP_TAC >>
REPEAT GEN_TAC >-
(rw [check_specs_def, success_eqns, bind_def] >>
 metis_tac []) >>
STRIP_TAC >>
REPEAT GEN_TAC >>
STRIP_TAC >>
REPEAT GEN_TAC >>
STRIP_TAC >>
fs [check_specs_def, success_eqns, check_env_bind] >|
[metis_tac [t_to_freevars_check2],
 metis_tac [check_build_ctor_tenv, check_cenv_def, merge_def, EVERY_APPEND],
 fs [bind_def, check_cenv_def] >>
     metis_tac [],
 metis_tac []]);

val infer_top_sound = Q.store_thm ("infer_top_sound",
`!menv cenv env top st1 menv' cenv' env' st2.
  (infer_top menv cenv env top st1 = (Success (menv', cenv', env'), st2)) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  type_top (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) top (convert_menv menv') cenv' (convert_env2 env')`,
cases_on `top` >>
rw [infer_top_def, success_eqns, type_top_cases] >>
PairCases_on `v'` >>
fs [success_eqns] >>
rw [emp_def] >|
[PairCases_on `v'` >>
     fs [success_eqns] >>
     rw [emp_def, convert_menv_def, convert_env2_def] >>
     `type_ds (SOME s) (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) l v'0 (convert_env2 v'1)`
             by metis_tac [infer_ds_sound] >>
     MAP_EVERY qexists_tac [`v'0`, `convert_env2 v'1`] >>
     rw [] >|
     [rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem] >>
          metis_tac [],
      metis_tac [convert_menv_def, convert_env2_def],
      cases_on `o'` >>
          rw [] >>
          fs [check_signature_cases, check_signature_def, success_eqns] >-
          rw [convert_env2_def] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          rw [] >>
          `check_cenv [] ∧ check_env {} ([]:(tvarN, num # infer_t) env)` by rw [check_env_def, check_cenv_def] >>
          `check_env {} v'1 ∧ check_env {} v'1'` by metis_tac [infer_ds_check, check_specs_check] >-
          metis_tac [check_weakE_sound, convert_env2_def] >-
          metis_tac [check_weakC_sound] >>
          imp_res_tac check_specs_sound >>
          fs [convert_env2_def, emp_def]],
 rw [convert_menv_def],
 metis_tac [infer_d_sound]]);

val infer_top_invariant = Q.store_thm ("infer_top_invariant",
`!menv cenv env top st1 menv' cenv' env' st2.
  (infer_top menv cenv env top st1 = (Success (menv', cenv', env'), st2)) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  check_menv menv' ∧
  check_cenv cenv' ∧
  check_env {} env'`,
cases_on `top` >|
[cases_on `o'` >|
     [rw [infer_top_def, success_eqns] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          fs [check_signature_def, success_eqns] >>
          rw [] >>
          `check_cenv cenv' ∧ check_env {} v'1` by metis_tac [infer_ds_check] >>
          rw [check_menv_def, check_env_def, emp_def] >>
          fs [check_env_def],
      rw [infer_top_def, success_eqns] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          fs [check_signature_def, success_eqns] >>
          rw [] >>
          PairCases_on `v'` >>
          fs [success_eqns] >>
          rw [] >>
          `check_cenv [] ∧ check_env {} ([]:(tvarN, num # infer_t) env)` by rw [check_env_def, check_cenv_def] >>
          `check_cenv cenv' ∧ check_env {} v'1'` by metis_tac [check_specs_check] >>
          rw [check_menv_def, check_env_def, emp_def] >>
          fs [check_env_def]],
 rw [infer_top_def, success_eqns] >>
     PairCases_on `v'` >>
     fs [success_eqns] >>
     rw [] >>
     TRY(rw[check_menv_def,emp_def]>>NO_TAC)>>
     metis_tac [infer_d_check]]);

val infer_init_thm = Q.store_thm ("infer_init_thm",
`check_menv [] ∧ check_cenv [] ∧ check_env {} init_type_env ∧
 (convert_menv [] = []) ∧
 (bind_var_list2 (convert_env2 init_type_env) Empty = init_tenv)`,
rw [check_t_def, check_menv_def, check_cenv_def, check_env_def, init_type_env_def,
    Infer_Tfn_def, Infer_Tint_def, Infer_Tbool_def, Infer_Tunit_def, 
    Infer_Tref_def, init_tenv_def, bind_var_list2_def, convert_env2_def,
    convert_t_def, convert_menv_def, bind_tenv_def, Tfn_def, Tint_def, Tbool_def,
    Tunit_def, Tref_def]);

val _ = export_theory ();
