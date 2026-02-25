(*
  This refines the distributed RUP checker to a TODO
*)
Theory distrup_list
Ancestors
  cnf ccnf distrup ccnf_list
Libs
  preamble

(*
  TODO: Unrefined hashtable version
  TODO: move to ccnf_list and
  rename everything consistently
Definition unit_prop_one_def:
  unit_prop_one fml dml b i =
  case FLOOKUP fml i of
    NONE => NONE
  | SOME c =>
    delete_literals_sing_list dml b c (length c)
End

Definition unit_prop_list_def:
  (unit_prop_list fml dml b [] = SOME (F,dml)) ∧
  (unit_prop_list fml dml b (i::is) =
  case unit_prop_one fml dml b i of
    NONE => NONE
  | SOME (T,dml') => SOME (T,dml')
  | SOME (F,dml') => unit_prop_list fml dml' b is)
End

Definition is_rup_list_def:
  is_rup_list fml dml b v is =
  let (dml',b') = prepare_rup dml b v in
  case unit_prop_list fml dml' b' is of
    SOME (T,dml'') => (T,dml'',b')
  | _ => (F, (dml',b'))
End

Theorem is_rup_list:
  dm_rel dm dml b ∧
  is_rup_list fml dml b v is = (T, (dml',b')) ⇒
  is_rup fml v is ∧
  ∃dm'. dm_rel dm' dml' b'

Definition bnd_fml_def:
  bnd_fml fml sz ⇔
  ∀v.
    v ∈ FRANGE fml ⇒
    bnd_clause v sz
End
*)

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

