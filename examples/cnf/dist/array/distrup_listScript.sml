(*
  This refines the distributed RUP checker to a TODO
*)
Theory distrup_list
Ancestors
  cnf ccnf distrup ccnf_list
Libs
  preamble

(* TODO: move to ccnf_list and
  rename everything consistently *)
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
Proof
  cheat
QED

Definition bnd_fml_def:
  bnd_fml fml sz ⇔
  ∀v.
    v ∈ FRANGE fml ⇒
    bnd_clause v sz
End

(* END MOVE *)

(* Refinement to make use of array representations *)
Definition check_distrup_list_def:
  check_distrup_list distrup fml dml b =
  case distrup of
  | Del ls =>
    SOME (delete_ids fml ls, (dml, b))
  | Lrup n vc hints =>
    (case is_rup_list fml dml b vc hints of
      (T, dmlb) =>
      SOME (fml |+ (n, vc) , dmlb)
    | _ => NONE)
  | Import n vc =>
      SOME (fml |+ (n, vc) , resize_dm dml b vc)
  | ValidateUnsat =>
    if contains_emp fml then
      SOME (fml, (dml,b))
    else NONE
End

Theorem check_distrup_list:
  dm_rel dm dml b ∧
  check_distrup_list distrup fml dml b =
    SOME (fml',(dml',b')) ⇒
  ∃dm'.
    check_distrup distrup fml = SOME fml' ∧
    dm_rel dm' dml' b'
Proof
  simp[check_distrup_list_def]>>strip_tac>>
  gvs[AllCaseEqs(),check_distrup_def]
  >- metis_tac[]
  >- (
    drule_all is_rup_list>>rw[])
  >- (
    gvs[resize_dm_def]>>
    drule_all dm_rel_reset_dm_list>>
    metis_tac[])
  >-
    metis_tac[]
QED

Theorem check_distrup_list_bnd_fml:
  bnd_fml fml (LENGTH dml) ∧
  check_distrup_list distrup fml dml b = SOME (fml',(dml',b')) ⇒
  bnd_fml fml' (LENGTH dml')
Proof
  simp[check_distrup_list_def]>>strip_tac>>
  gvs[AllCaseEqs(),check_distrup_def]
  >- cheat (* metis_tac[bnd_fml_delete_ids_list] *)
  >- (
    cheat
    (* drule_all bnd_fml_is_rup_list>>
    metis_tac[bnd_fml_update_resize]*))
  >- (
    cheat
    (*
    irule bnd_fml_update_resize>>
    drule bnd_clause_resize_dm>>
    simp[]>>
    rw[]>>irule bnd_fml_le>>
    metis_tac[resize_dm_LENGTH]*))
QED

