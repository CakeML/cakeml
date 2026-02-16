(*
  This refines the distributed RUP checker to a TODO
*)
Theory distrup_list
Ancestors
  cnf ccnf distrup ccnf_list
Libs
  preamble

Definition resize_dm_def:
  resize_dm dml b v =
  let lv = length v in
  let sz = sz_lit_map lv v 0 in
  reset_dm_list dml b sz
End

Theorem bnd_clause_resize_dm:
  resize_dm dml b v = (dml',b') ⇒
  bnd_clause v (LENGTH dml')
Proof
  rw[resize_dm_def]>>
  irule bnd_clause_le >>
  gvs[reset_dm_list_def,AllCaseEqs(),NOT_LESS] >>
  irule_at (Pos last) sz_lit_map_bnd_clause >>
  Q.EXISTS_TAC `0` >> fs[]
QED

Theorem resize_dm_LENGTH:
  resize_dm dml b v = (dml',b') ⇒
  LENGTH dml ≤ LENGTH dml'
Proof
  rw[resize_dm_def]>>
  drule_then strip_assume_tac reset_dm_list_LENGTH
QED

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
  rw[check_distrup_list_def]>>
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
QED

Theorem check_distrup_list_bnd_fml:
  bnd_fml fmlls (LENGTH dml) ∧
  check_distrup_list distrup fmlls dml b = SOME (fmlls',(dml',b')) ⇒
  bnd_fml fmlls' (LENGTH dml')
Proof
  rw[check_distrup_list_def]>>
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

