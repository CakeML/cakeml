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
      SOME (insert_vcc_list fml n vc, dmlb)
    | _ => NONE)
  | Import n vc =>
      SOME (insert_vcc_list fml n vc, resize_dm dml b vc)
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
    simp[fml_rel_insert_vcc_list]>>
    metis_tac[])
  >- (
    simp[fml_rel_insert_vcc_list]>>
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
    metis_tac[bnd_fml_insert_vcc_list])
  >- (
    irule bnd_fml_insert_vcc_list>>
    drule bnd_clause_resize_dm>>
    simp[]>>
    rw[]>>irule bnd_fml_le>>
    metis_tac[resize_dm_LENGTH])
QED


(* Unit propagation commits to the first non-falsified literal and then
  requires every other literal to be falsified, except that a repeat of the
  committed literal is allowed, so a clause carrying a repeated literal is
  still accepted when it is cited as a hint.

  Here "1 1" is imported as clause 1 and "-1" as clause 2, and the empty
  clause is derived by RUP from both. *)
Theorem check_distrup_list_dup_import[local]:
  (case check_distrup_list (Import 1 (Vector [1;1]))
      (REPLICATE 10 vcc_none) (REPLICATE 4 0w) 1w of
    NONE => F
  | SOME (fml1,dml1,b1) =>
  case check_distrup_list (Import 2 (Vector [-1])) fml1 dml1 b1 of
    NONE => F
  | SOME (fml2,dml2,b2) =>
  case check_distrup_list (Lrup 3 (Vector []) [1;2]) fml2 dml2 b2 of
    NONE => F
  | SOME (fml3,dml3,b3) => contains_emp_list fml3)
Proof
  EVAL_TAC
QED
