open preamble;
open environmentTheory;
open terminationTheory;

val _ = new_theory "environmentProps";

(* ----------- Monotonicity for Hol_reln ------------ *)

val eAll_mono = Q.store_thm ("eAll_mono",
  `(!id x. P id x ⇒ Q id x) ⇒ eAll P e ⇒ eAll Q e`,
  rw [eAll_def]);

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

val eAppend_eEmpty = Q.store_thm ("eAppend_eEmpty[simp]",
  `!env. eAppend env eEmpty = env ∧ eAppend eEmpty env = env`,
 Cases
 >> rw [eAppend_def, eEmpty_def]);

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

(* ------------- Other simple automatic theorems --------- *)

val alist_to_env_cons = Q.store_thm ("alist_to_env_cons[simp]",
  `!k v l. alist_to_env ((k,v)::l) = eBind k v (alist_to_env l)`,
 rw [alist_to_env_def, eBind_def]);

val eAppend_eBind = Q.store_thm ("eAppend_eBind[simp]",
  `!k v e1 e2. eAppend (eBind k v e1) e2 = eBind k v (eAppend e1 e2)`,
 Cases_on `e1`
 >> Cases_on `e2`
 >> rw [eAppend_def, eBind_def]);

val eAppend_alist_to_env = Q.store_thm ("eAppend_alist_to_env[simp]",
  `!al1 al2. eAppend (alist_to_env al1) (alist_to_env al2) = alist_to_env (al1 ++ al2)`,
 rw [alist_to_env_def, eAppend_def]);

val eAppend_assoc = Q.store_thm ("eAppend_assoc[simp]",
  `!e1 e2 e3. eAppend e1 (eAppend e2 e3) = eAppend (eAppend e1 e2) e3`,
 rpt Cases
 >> rw [eAppend_def]);

(* -------------- eAll ---------------- *)

val eLookup_eAll = Q.store_thm ("eLookup_eAll",
  `!env x P v. eAll P env ∧ eLookup env x = SOME v ⇒ P x v`,
 rw [eAll_def]);

val eAll_eAppend = Q.store_thm ("eAll_eAppend",
  `!f e1 e2. eAll f e1 ∧ eAll f e2 ⇒ eAll f (eAppend e1 e2)`,
 simp [eAll_def, PULL_FORALL]
 >> rpt gen_tac
 >> qspec_tac (`v`, `v`)
 >> qspec_tac (`e2`, `e2`)
 >> qspec_tac (`id`, `id`)
 >> qspec_tac (`e1`, `e1`)
 >> ho_match_mp_tac eLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [eAppend_def, eLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [GSYM PULL_FORALL]
 >- metis_tac [eLookup_def]
 >- metis_tac [eLookup_def]
 >> rw []
 >> rpt (first_x_assum (qspec_then `Long mn id` mp_tac))
 >> simp [eLookup_def]);

(* -------------- eSubEnv ---------------- *)

val eSubEnv_conj = Q.store_thm ("eSubEnv_conj",
  `!P Q e1 e2. eSubEnv (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ eSubEnv P e1 e2 ∧ eSubEnv Q e1 e2`,
 rw [eSubEnv_def]
 >> eq_tac
 >> rw []
 >> metis_tac [SOME_11]);

(* -------------- eAll2 ---------------- *)

val eAll2_conj = Q.store_thm ("eAll2_conj",
  `!P Q e1 e2. eAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ eAll2 P e1 e2 ∧ eAll2 Q e1 e2`,
 rw [eAll2_def, eSubEnv_conj]);

val _ = export_theory ();
