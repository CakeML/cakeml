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
      SOME (insert_vcc_list fml n C, dml', b')
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
  simp[fml_rel_insert_vcc_list]>>
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
  metis_tac[bnd_fml_insert_vcc_list]
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
    (build_cfml_list kc (conv_cfml cfml) nc)
    (REPLICATE n 0w) 1w ∧
  EVERY (EVERY nz_lit) cfml ⇒
  unsatisfiable_cnf (set cfml)
Proof
  strip_tac>>
  irule check_lrups_unsat_conv_sound>>
  simp[]>>
  qexistsl_tac [`kc`,`lrups`]>>
  irule check_lrups_unsat_list>>
  rpt (first_x_assum (irule_at Any))>>
  irule_at Any fml_rel_build_cfml_list>>
  irule_at Any dm_rel_FEMPTY_REPLICATE>>
  metis_tac[]
QED

(* Unit propagation commits to the first non-falsified literal and then
  requires every other literal to be falsified, except that a repeat of the
  committed literal is allowed, so a clause carrying a repeated literal is
  still accepted when it is cited as a hint.

  Records are NUL-separated, and the variable-byte encoding of 0 is the NUL
  byte itself, so a record carries no terminator of its own: the literals
  end at the end of the chunk. Literals are doubled (+k as 2k, -k as 2k+1)
  and so are the clause ids. *)

(* p cnf 1 2 / "1 1 0" / "-1 0", refuted by the empty clause with id 3
  from hints 1 and 2. Hint 1 is the input clause repeating a literal. *)
Theorem check_lrups_unsat_list_dup_cnf[local]:
  check_lrups_unsat_list
    (THE (parse_lrups [implode (MAP CHR [97;6]); implode (MAP CHR [2;4])]))
    (build_cfml_list 1 (conv_cfml [[Pos 1; Pos 1]; [Neg 1]]) 10)
    (REPLICATE 4 0w) 1w
Proof
  EVAL_TAC
QED

(* p cnf 2 3 / "1 2 0" / "1 -2 0" / "-1 0". Clause 4 = "1 1" is derived by
  RUP from 1 and 2, then the empty clause with id 5 from hints 4 and 3.
  Hint 4 is a derived clause repeating a literal. *)
Theorem check_lrups_unsat_list_dup_derived[local]:
  check_lrups_unsat_list
    (THE (parse_lrups
      [implode (MAP CHR [97;8;2;2]); implode (MAP CHR [2;4]);
       implode (MAP CHR [97;10]);    implode (MAP CHR [8;6])]))
    (build_cfml_list 1
      (conv_cfml [[Pos 1; Pos 2]; [Pos 1; Neg 2]; [Neg 1]]) 10)
    (REPLICATE 4 0w) 1w
Proof
  EVAL_TAC
QED
