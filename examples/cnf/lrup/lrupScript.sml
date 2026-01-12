(*
   Basic specification of an LRUP checker
*)
Theory lrup
Libs
  preamble
Ancestors
  ccnf cnf

(* The LRUP format only has two proof steps. *)
Datatype:
  lrup =
  | Del (num list) (* Clauses to delete *)
  | Lrup num vcclause (num list)
    (* Lrup n C hints : derive clause C by RUP using hints *)
  | Lrupvb num vcclause mlstring
    (* Lrupvb n C hints : derive clause C by RUP using hints,
        hints are passed in raw vb-encoded mlstring. *)
End

Definition check_lrup_def:
  check_lrup lrup fml =
  case lrup of
    Del ls =>
    SOME (delete_ids fml ls)
  | Lrup n vc hints =>
    if is_rup fml vc hints
    then
      SOME (insert n vc fml)
    else NONE
  | Lrupvb n vc hints => NONE
End

Definition check_lrups_def:
  (check_lrups [] fml = SOME fml) ∧
  (check_lrups (x::xs) fml =
  case check_lrup x fml of
    NONE => NONE
  | SOME cfml' =>
    check_lrups xs cfml')
End

Theorem check_lrup_sound:
  check_lrup lrup fml = SOME fml' ∧
  satisfies_vcfml w (range fml)
  ⇒
  satisfies_vcfml w (range fml')
Proof
  simp[check_lrup_def]>>strip_tac>>
  gvs[AllCaseEqs()]
  >- (
    (* deleting clauses by ID *)
    fs[satisfies_vcfml_def]>>
    metis_tac[satisfies_fml_gen_delete_ids])
  >- (
    drule is_rup_sound>>
    disch_then $ drule_at Any>>
    fs[satisfies_vcfml_def]>>
    metis_tac[satisfies_fml_gen_insert])
QED

(* The main operational theorem about check_lrups *)
Theorem check_lrups_sound:
  ∀ls fml fml'.
  check_lrups ls fml = SOME fml' ∧
  satisfies_vcfml w (range fml)
  ⇒
  satisfies_vcfml w (range fml')
Proof
  Induct>>simp[check_lrups_def]>>
  rw[]>>
  gvs[AllCaseEqs()]>>
  drule check_lrup_sound>>
  disch_then drule>>
  strip_tac>>
  first_x_assum drule_all>>
  metis_tac[]
QED

Definition check_lrups_unsat_def:
  check_lrups_unsat ls fml =
  (case check_lrups ls fml of
    NONE => F
  | SOME fml' => contains_emp fml')
End

(* Main theorem *)
Theorem check_lrups_unsat_sound:
  check_lrups_unsat ls (build_fml cid cfml) ⇒
  ¬ ∃w.
    satisfies_vcfml w (set cfml)
Proof
  rw[check_lrups_unsat_def]>>
  CCONTR_TAC>>
  gvs[AllCasePreds()]>>
  drule check_lrups_sound>>
  simp[range_build_fml]>>
  metis_tac[contains_emp_unsat]
QED

