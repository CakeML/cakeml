(*
  This refines the LRUP checker to a fixed-size, list-based implementation
*)
Theory lrup_list
Ancestors
  cnf ccnf lrup ccnf_list
Libs
  preamble

(* Refinement to make use of array representations *)
Definition check_lrup_list_def:
  check_lrup_list lrup fml dml b =
  case lrup of
    Skip => SOME (fml, (dml, b))
  | Del ls =>
    SOME (delete_ids_list fml ls, (dml, b))
  | Lrup n vc hints =>
    (case is_rup_list fml dml b vc hints of
      (T, dmlb) =>
      SOME (update_resize fml NONE (SOME vc) n, dmlb)
    | _ => NONE)
  | _ => NONE
End

Theorem check_lrup_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  check_lrup_list lrup fmlls dml b = SOME (fmlls',(dml',b')) ⇒
  ∃fml' dm'.
    check_lrup lrup fml = SOME fml' ∧
    fml_rel fml' fmlls' ∧
    dm_rel dm' dml' b'
Proof
  rw[check_lrup_list_def]>>
  gvs[AllCaseEqs(),check_lrup_def]
  >- metis_tac[]
  >- (simp[fml_rel_delete_ids_list]>>metis_tac[])
  >- (
    drule_all is_rup_list>>rw[]>>
    simp[fml_rel_update_resize]>>
    metis_tac[])
QED

Theorem check_lrup_list_bnd_fml:
  bnd_fml fmlls (LENGTH dml) ∧
  check_lrup_list lrup fmlls dml b = SOME (fmlls',(dml',b')) ⇒
  bnd_fml fmlls' (LENGTH dml')
Proof
  rw[check_lrup_list_def]>>
  gvs[AllCaseEqs(),check_lrup_def]
  >- metis_tac[bnd_fml_delete_ids_list]
  >- (
    drule_all bnd_fml_is_rup_list>>
    metis_tac[bnd_fml_update_resize])
QED

