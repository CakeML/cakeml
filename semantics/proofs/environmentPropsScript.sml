open preamble;
open environmentTheory;
open terminationTheory;

val _ = new_theory "environmentProps";

(* ----------- Monotonicity for Hol_reln ------------ *)

val eAll_mono_lemma = Q.prove (
  `!f1 e. (!x. f1 x ⇒ f2 x) ⇒ eAll f1 e ⇒ eAll f2 e`,
  ho_match_mp_tac eAll_ind
  >> rw [eAll_def, EVERY_MEM]);

val eAll_mono = save_thm ("eAll_mono", SPEC_ALL eAll_mono_lemma);

val eSubEnv_mono = Q.store_thm ("eSubEnv_mono",
  `(!x y z. R1 x y z ⇒ R2 x y z) ⇒ (eSubEnv R1 e1 e2 ⇒ eSubEnv R2 e1 e2)`,
 Cases_on `e1`
 >> Cases_on `e2`
 >> simp [eSubEnv_def, eLookup_def]
 >> rw []
 >> metis_tac []);

val eAll2_mono = Q.store_thm ("eAll2_mono",
  `(!x y z. R1 x y z ⇒ R2 x y z) ⇒ eAll2 R1 e1 e2 ⇒ eAll2 R2 e1 e2`,
 rw [eAll2_def]
 >> metis_tac [eSubEnv_mono]);

val _ = export_mono "eAll_mono";
val _ = export_mono "eSubEnv_mono";
val _ = export_mono "eAll2_mono";

(* ---------- Automatic simps involving empty envs -------------- *)

val eLookup_eEmpty = Q.store_thm ("eLookup_eEmpty[simp]",
  `!id. eLookup eEmpty id = NONE`,
 Cases
 >> rw [eLookup_def, eEmpty_def]);

val eMerge_eEmpty = Q.store_thm ("eMerge_eEmpty[simp]",
  `!env. eMerge env eEmpty = env ∧ eMerge eEmpty env = env`,
 Cases
 >> rw [eMerge_def, eEmpty_def]);

val alist_to_env_nil = Q.store_thm ("alist_to_env_nil[simp]",
  `alist_to_env [] = eEmpty`,
 rw [alist_to_env_def, eEmpty_def]);

val eSubEnv_eEmpty = Q.store_thm ("eSubEnv_eEmpty[simp]",
  `!r env. eSubEnv r eEmpty env`,
 rw [eSubEnv_def]);

val eAll_eEmpty = Q.store_thm ("eAll_eEmpty[simp]",
  `!f. eAll f eEmpty`,
 rw [eEmpty_def, eAll_def]);

val eAll2_eEmpty = Q.store_thm ("eAll2_eEmpty[simp]",
  `!f. eAll2 f eEmpty eEmpty`,
 rw [eEmpty_def, eAll2_def]);

val eDom_eEmpty = Q.store_thm ("eDom_eEmpty[simp]",
  `eDom eEmpty = {}`,
 rw [eDom_def, eEmpty_def, EXTENSION, GSPECIFICATION]
 >> pairarg_tac
 >> rw []);

val eMap_eEmpty = Q.store_thm ("eMap_eEmpty[simp]",
  `!f. eMap f eEmpty = eEmpty`,
 rw [eMap_def, eEmpty_def]);

(* ------------- Other automatic theorems --------- *)

val alist_to_env_cons = Q.store_thm ("alist_to_env_cons[simp]",
  `!k v l. alist_to_env ((k,v)::l) = eBind k v (alist_to_env l)`,
 rw [alist_to_env_def, eBind_def]);

val eMerge_eBind = Q.store_thm ("eMerge_eBind[simp]",
  `!k v e1 e2. eMerge (eBind k v e1) e2 = eBind k v (eMerge e1 e2)`,
 Cases_on `e1`
 >> Cases_on `e2`
 >> rw [eMerge_def, eBind_def]);

val eMerge_alist_to_env = Q.store_thm ("eMerge_alist_to_env[simp]",
  `!al1 al2. eMerge (alist_to_env al1) (alist_to_env al2) = alist_to_env (al1 ++ al2)`,
 rw [alist_to_env_def, eMerge_def]);

val eMerge_assoc = Q.store_thm ("eMerge_assoc[simp]",
  `!e1 e2 e3. eMerge e1 (eMerge e2 e3) = eMerge (eMerge e1 e2) e3`,
 rpt Cases
 >> rw [eMerge_def]);

val _ = export_theory ();
