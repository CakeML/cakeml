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

val eLookup_eBind = Q.store_thm ("eLookup_eBind[simp]",
  `(!n v e. eLookup (eBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ eLookup (eBind n' v e) n = eLookup e n)`,
 rw []
 >> Cases_on `e`
 >> TRY (Cases_on `n`)
 >> rw [eLookup_def, eBind_def]);

(* --------------- eAppend ------------- *)

val eLookup_eAppend_none = Q.store_thm ("eLookup_eAppend_none",
  `∀e1 id e2.
    eLookup e1 id = NONE ∧ eLookup e2 id = NONE
    ⇒
    eLookup (eAppend e1 e2) id = NONE`,
 ho_match_mp_tac eLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [eAppend_def, eLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []);

val eLookup_eAppend_some = Q.store_thm ("eLookup_eAppend_some",
  `∀e1 id e2 v.
    eLookup (eAppend e1 e2) id = SOME v
    ⇒
    eLookup e1 id = SOME v ∨ (eLookup e1 id = NONE ∧ eLookup e2 id = SOME v)`,
 ho_match_mp_tac eLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [eAppend_def, eLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []);

val eLookup_eAppend1 = Q.store_thm ("eLookup_eAppend1[simp]",
  `∀e1 id e2 v.
    eLookup e1 id = SOME v
    ⇒
    eLookup (eAppend e1 e2) id = SOME v`,
 ho_match_mp_tac eLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [eAppend_def, eLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []);

(* -------------- eAll ---------------- *)

val eAll_T = Q.store_thm ("eALL_T[simp]",
  `!e. eAll (\n x. T) e`,
 rw [eAll_def]);

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

val eAll_eBind = Q.store_thm ("eAll_eBind",
  `!P x v e. P (Short x) v ∧ eAll P e ⇒ eAll P (eBind x v e)`,
 rw [eAll_def, eBind_def]
 >> Cases_on `id = Short x`
 >> fs []);

(* -------------- eSubEnv ---------------- *)

val eSubEnv_conj = Q.store_thm ("eSubEnv_conj",
  `!P Q e1 e2. eSubEnv (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ eSubEnv P e1 e2 ∧ eSubEnv Q e1 e2`,
 rw [eSubEnv_def]
 >> eq_tac
 >> rw []
 >> metis_tac [SOME_11]);

val eSubEnv_refl = Q.store_thm ("eSubEnv_refl",
  `!P R. (!n x. P n x ⇒ R n x x) ⇒ !e. eAll P e ⇒ eSubEnv R e e`,
 rw [eSubEnv_def]
 >> metis_tac [eLookup_eAll]);

val eSubEnv_eBind = Q.store_thm ("eSubEnv_eBind",
  `!R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ eSubEnv R e1 e2 ⇒ eSubEnv R (eBind x v1 e1) (eBind x v2 e2)`,
 rw [eBind_def, eSubEnv_def]
 >> Cases_on `id = Short x`
 >> fs []);

(* -------------- eAll2 ---------------- *)

val eAll2_conj = Q.store_thm ("eAll2_conj",
  `!P Q e1 e2. eAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ eAll2 P e1 e2 ∧ eAll2 Q e1 e2`,
 rw [eAll2_def, eSubEnv_conj]
 >> metis_tac []);

val eAll2_eLookup1 = Q.store_thm ("eAll2_eLookup1",
  `!R e1 e2 n v1.
    eLookup e1 n = SOME v1 ∧
    eAll2 R e1 e2
    ⇒
    ?v2. eLookup e2 n = SOME v2 ∧ R n v1 v2`,
 rw [eSubEnv_def, eAll2_def]);

val eAll2_eLookup2 = Q.store_thm ("eAll2_eLookup2",
  `!R e1 e2 n v2.
    eLookup e2 n = SOME v2 ∧
    eAll2 R e1 e2
    ⇒
    ?v1. eLookup e1 n = SOME v1 ∧ R n v1 v2`,
 rw [eSubEnv_def, eAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]);

val eAll2_eLookup_none = Q.store_thm ("eAll2_eLookup_none",
  `!R e1 e2 n.
    eAll2 R e1 e2
    ⇒
    (eLookup e1 n = NONE ⇔ eLookup e2 n = NONE)`,
 rw [eSubEnv_def, eAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]);

val eAll2_eBind = Q.store_thm ("eAll2_eBind",
  `!R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ eAll2 R e1 e2 ⇒ eAll2 R (eBind x v1 e1) (eBind x v2 e2)`,
 rw [eAll2_def]
 >- metis_tac [eSubEnv_eBind]
 >> Cases_on `n = Short x`
 >> fs []);

val _ = export_theory ();
