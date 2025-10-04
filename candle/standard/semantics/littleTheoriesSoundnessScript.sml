(*
  Proves soundness of the inference system: any provable sequent is valid.
*)
open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
              littleTheoriesSyntaxTheory 
              littleTheoriesSyntaxOldSystemTheory
              littleTheoriesSyntaxNewSystemTheory
              holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory

val _ = new_theory"littleTheoriesSoundness"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U-> bool``

Triviality type_ok_ctys[simp]:
  theory_ok' thy ∧
  ty ∈ FRANGE thy.ctms ⇒
  type_ok thy.ctys ty
Proof
  rw[theory_ok'_def, ctys_def, ctms_def]
  >> gvs[FRANGE_FUNION] >> first_x_assum drule
  >> simp[type_ok_weakening]
QED
    
Theorem elim_discharge_correct:
   is_set_theory ^mem ⇒
   ∀thy c. theory_ok' thy ∧ c ∈ thy.eaxs ⇒
           (drop_thy {c} thy,[]) |= c
Proof
  rw[entails_def,theory_ok_def,models_def,drop_thy]
QED

Theorem proves'_sound:
  is_set_theory ^mem ⇒
  ∀thy used_eaxs h c. (thy, used_eaxs, h) |-' c ⇒ (drop_thy used_eaxs thy, h) |= c
Proof
  Induct_on ‘$|-'’ >> rw[drop_thy] >> gvs[]
  >- (irule ABS_correct >> simp[])
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- (rw[entails_def,theory_ok_def,models_def] >> cheat)
  >- ()
  >> cheat
  
QED

val _ = export_theory()
