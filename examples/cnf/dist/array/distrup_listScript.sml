(*
  This refines the distributed RUP checker to a list-based impl.
*)
Theory distrup_list
Ancestors
  cnf ccnf distrup ccnf_list
Libs
  preamble

(* Refinement to make use of array representations *)
Definition check_distrup_list_def:
  check_distrup_list distrup fml dml b =
  case distrup of
  | Del ls =>
    SOME (delete_ids_list fml ls, (dml, b))
  | Lrup n vc hints =>
    (case is_rup_list fml dml b vc hints of
      (T, dmlb) =>
      SOME (update_resize fml NONE (SOME vc) n, dmlb)
    | _ => NONE)
  | Import n vc =>
      SOME (update_resize fml NONE (SOME vc) n, resize_dm dml b vc)
  | ValidateUnsat =>
    if contains_emp_list fml then
      SOME (fml, (dml,b))
    else NONE
End

Theorem check_distrup_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  check_distrup_list distrup fmlls dml b = SOME (fmlls',(dml',b')) ⇒
  ∃fml' dm'.
    check_distrup distrup fml = SOME fml' ∧
    fml_rel fml' fmlls' ∧
    dm_rel dm' dml' b'
Proof
  simp[check_distrup_list_def]>>strip_tac>>
  gvs[AllCaseEqs(),check_distrup_def]
  >- (simp[fml_rel_delete_ids_list]>>metis_tac[])
  >- (
    drule_all is_rup_list>>rw[]>>
    simp[fml_rel_update_resize]>>
    metis_tac[])
  >- (
    simp[fml_rel_update_resize]>>
    gvs[resize_dm_def]>>
    drule_all dm_rel_reset_dm_list>>
    metis_tac[])
  >-
    metis_tac[fml_rel_contains_emp_list]
QED

Theorem check_distrup_list_bnd_fml:
  bnd_fml fmlls (LENGTH dml) ∧
  check_distrup_list distrup fmlls dml b = SOME (fmlls',(dml',b')) ⇒
  bnd_fml fmlls' (LENGTH dml')
Proof
  simp[check_distrup_list_def]>>strip_tac>>
  gvs[AllCaseEqs(),check_distrup_def]
  >- metis_tac[bnd_fml_delete_ids_list]
  >- (
    drule_all bnd_fml_is_rup_list>>
    metis_tac[bnd_fml_update_resize])
  >- (
    irule bnd_fml_update_resize>>
    drule bnd_clause_resize_dm>>
    simp[]>>
    rw[]>>irule bnd_fml_le>>
    metis_tac[resize_dm_LENGTH])
QED

