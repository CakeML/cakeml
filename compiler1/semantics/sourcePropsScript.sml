open preamble rich_listTheory semanticPrimitivesTheory astTheory evalPropsTheory
open terminationTheory

(* TODO: this theory should be moved entirely into evalPropsTheory and/or other
         things under (top-level) semantics/proofs *)

val _ = new_theory"sourceProps"

val pmatch_extend = Q.store_thm("pmatch_extend",
`(!cenv s p v env env' env''.
  pmatch cenv s p v env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
 (!cenv s ps vs env env' env''.
  pmatch_list cenv s ps vs env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])`,
 ho_match_mp_tac pmatch_ind >>
 rw [pat_bindings_def, pmatch_def] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 qexists_tac `env'''++env''` >>
 rw [] >>
 metis_tac [pat_bindings_accum]);

val mk_id_11 = Q.store_thm("mk_id_11[simp]",
  `mk_id a b = mk_id c d ⇔ (a = c) ∧ (b = d)`,
  map_every Cases_on[`a`,`c`] >> EVAL_TAC)

val Boolv_11 = store_thm("Boolv_11[simp]",``Boolv b1 = Boolv b2 ⇔ (b1 = b2)``,rw[Boolv_def]);

val find_recfun_el = Q.store_thm("find_recfun_el",
  `!f funs x e n.
    ALL_DISTINCT (MAP (\(f,x,e). f) funs) ∧
    n < LENGTH funs ∧
    EL n funs = (f,x,e)
    ⇒
    find_recfun f funs = SOME (x,e)`,
  simp[find_recfun_ALOOKUP] >>
  induct_on `funs` >>
  rw [] >>
  cases_on `n` >>
  fs [] >>
  PairCases_on `h` >>
  fs [] >>
  rw [] >>
  res_tac >>
  fs [MEM_MAP, MEM_EL, FORALL_PROD] >>
  metis_tac []);

val same_tid_refl = store_thm("same_tid_refl[simp]",
  ``same_tid t t``,
  Cases_on`t`>>EVAL_TAC);

val same_tid_diff_ctor = Q.store_thm("same_tid_diff_ctor",
  `!cn1 cn2 t1 t2.
    same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
    ⇒
    (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)`,
  rw [] >>
  cases_on `t1` >>
  cases_on `t2` >>
  fs [same_tid_def, same_ctor_def]);

val same_tid_tid = Q.store_thm("same_tid_tid",
  `(same_tid (TypeId x) y ⇔ (y = TypeId x)) ∧
   (same_tid y (TypeId x) ⇔ (y = TypeId x))`,
  Cases_on`y`>>EVAL_TAC>>rw[EQ_IMP_THM])

val merge_alist_mod_env_empty = Q.store_thm("merge_alist_mod_env_empty",
  `!mod_env. merge_alist_mod_env ([],[]) mod_env = mod_env`,
  rw [] >>
  PairCases_on `mod_env` >>
  rw [merge_alist_mod_env_def]);

val MAP_FST_build_tdefs = store_thm("MAP_FST_build_tdefs",
  ``set (MAP FST (build_tdefs mn ls)) =
    set (MAP FST (FLAT (MAP (SND o SND) ls)))``,
  Induct_on`ls`>>simp[build_tdefs_cons] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[build_tdefs_cons,MAP_REVERSE] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  metis_tac[UNION_COMM])

val _ = export_theory()
