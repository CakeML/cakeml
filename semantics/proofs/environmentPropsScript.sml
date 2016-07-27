open preamble;
open environmentTheory;
open terminationTheory;

val _ = new_theory "environmentProps";

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

val _ = export_theory ();
