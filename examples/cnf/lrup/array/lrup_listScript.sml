(*
  This refines the LRUP checker to a list-based implementation.
*)
Theory lrup_list
Ancestors
  cnf ccnf lrup_cnf lrup ccnf_list mlstring mlvector
Libs
  preamble

Definition check_lrup_list_def:
  check_lrup_list lrup fml dml b =
  case lrup of
    Delvb s =>
    SOME (delete_ids_vb_list fml s 1 (strlen s), dml, b)
  | Lrupvb n C s =>
    (case is_rup_vb_list fml dml b C s of
      (T, dml', b') =>
      SOME (update_resize fml NONE (SOME C) n, dml', b')
    | _ => NONE)
End

Theorem check_lrup_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  check_lrup_list lrup fmlls dml b = SOME (fmlls', dml', b') ⇒
  ∃fml' dm'.
    check_lrup lrup fml = SOME fml' ∧
    fml_rel fml' fmlls' ∧
    dm_rel dm' dml' b'
Proof
  simp[check_lrup_def,check_lrup_list_def]>>
  strip_tac>>
  Cases_on`lrup`>>gvs[AllCaseEqs()]
  >- (* Delvb *)
    (simp[fml_rel_delete_ids_vb_list]>>metis_tac[])>>
  (* Lrupvb *)
  drule_all is_rup_vb_list>>rw[]>>
  simp[fml_rel_update_resize]>>
  metis_tac[]
QED

Theorem check_lrup_list_bnd_fml:
  bnd_fml fmlls (LENGTH dml) ∧
  check_lrup_list lrup fmlls dml b = SOME (fmlls', dml', b') ⇒
  bnd_fml fmlls' (LENGTH dml')
Proof
  simp[check_lrup_list_def]>>
  strip_tac>>
  Cases_on`lrup`>>gvs[AllCaseEqs()]
  >- metis_tac[bnd_fml_delete_ids_vb_list]>>
  drule_all bnd_fml_is_rup_vb_list>>
  metis_tac[bnd_fml_update_resize]
QED

Definition check_lrups_list_def:
  (check_lrups_list [] fml dml b = SOME fml) ∧
  (check_lrups_list (x::xs) fml dml b =
    case check_lrup_list x fml dml b of
      NONE => NONE
    | SOME (fml', dml', b') =>
      check_lrups_list xs fml' dml' b')
End

Theorem check_lrups_list:
  ∀lrups fml fmlls fmlls' dml b dm.
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  check_lrups_list lrups fmlls dml b = SOME fmlls' ⇒
  ∃fml'.
    check_lrups lrups fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lrups_list_def,check_lrups_def]>>
  rw[]>>gvs[AllCaseEqs()]>>
  drule check_lrup_list>>
  rpt (disch_then drule)>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]>>
  metis_tac[]
QED

Definition check_lrups_unsat_list_def:
  check_lrups_unsat_list lrups fml dml b =
  case check_lrups_list lrups fml dml b of
    NONE => F
  | SOME fml' => contains_emp_list fml'
End

Theorem check_lrups_unsat_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  check_lrups_unsat_list lrups fmlls dml b ⇒
  check_lrups_unsat lrups fml
Proof
  simp[check_lrups_unsat_list_def,check_lrups_unsat_def]>>
  strip_tac>>
  Cases_on`check_lrups_list lrups fmlls dml b`>>
  gvs[]>>
  drule_all check_lrups_list>>
  strip_tac>>gvs[]>>
  metis_tac[fml_rel_contains_emp_list]
QED

(* The checker's guarantee at the list level, phrased on the parsed
  formula rather than on the checker's internal representation *)
Theorem check_lrups_unsat_list_sound:
  check_lrups_unsat_list lrups
    (build_fml_list kc (conv_cfml cfml) nc)
    (REPLICATE n 0w) 1w ∧
  EVERY (EVERY nz_lit) cfml ⇒
  sols cfml = {}
Proof
  strip_tac>>
  irule check_lrups_unsat_conv_sound>>
  simp[]>>
  qexistsl_tac [`kc`,`lrups`]>>
  irule check_lrups_unsat_list>>
  rpt (first_x_assum (irule_at Any))>>
  irule_at Any fml_rel_build_fml_list>>
  irule_at Any dm_rel_FEMPTY_REPLICATE>>
  metis_tac[]
QED
