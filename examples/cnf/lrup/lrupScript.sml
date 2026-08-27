(*
   Specification of an LRUP checker for CNF
*)
Theory lrup
Ancestors
  cnf ccnf syntax_helper lrup_cnf mlstring mlvector
Libs
  preamble

(* The compressed LRUP format has two proof steps. Both carry the raw
  variable-byte encoded bytes of the record they were read from, so that
  neither the deleted ids nor the RUP hints are ever materialised. *)
Datatype:
  lrup =
  | Delvb mlstring
    (* Delvb s : delete the clause ids encoded in s *)
  | Lrupvb num vcclause mlstring
    (* Lrupvb n C s : derive clause C by RUP using the hints encoded in s *)
End

Definition check_lrup_def:
  check_lrup lrup fml =
  case lrup of
    (* The record tag occupies the first byte, so the ids start at 1 *)
    Delvb s =>
    SOME (delete_ids_vb fml s 1 (strlen s))
  | Lrupvb n vc s =>
    if is_rup_vb fml vc s
    then
      SOME (insert_vcc fml n vc)
    else NONE
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
  satisfies_vcfml w (FRANGE fml)
  ⇒
  satisfies_vcfml w (FRANGE fml')
Proof
  simp[check_lrup_def]>>strip_tac>>
  gvs[AllCaseEqs()]
  >- (
    (* deleting clauses by ID *)
    fs[satisfies_vcfml_def]>>
    metis_tac[satisfies_fml_gen_delete_ids_vb])>>
  drule is_rup_vb_sound>>
  disch_then $ drule_at Any>>
  fs[satisfies_vcfml_def,insert_vcc_def]>>
  metis_tac[SRULE [] satisfies_fml_gen_insert,satisfies_vcclause_canon_vcc]
QED

(* The main operational theorem about check_lrups *)
Theorem check_lrups_sound:
  ∀ls fml fml'.
  check_lrups ls fml = SOME fml' ∧
  satisfies_vcfml w (FRANGE fml)
  ⇒
  satisfies_vcfml w (FRANGE fml')
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

Theorem check_lrups_unsat_sound:
  check_lrups_unsat ls (build_cfml cid cfml) ⇒
  ¬ ∃w.
    satisfies_vcfml w (set cfml)
Proof
  rw[check_lrups_unsat_def]>>
  CCONTR_TAC>>
  gvs[AllCasePreds()]>>
  drule check_lrups_sound>>
  simp[range_build_cfml]>>
  metis_tac[contains_emp_unsat]
QED

(* The checker's guarantee, phrased on the parsed formula rather than on
  the checker's internal representation *)
Theorem check_lrups_unsat_conv_sound:
  EVERY (EVERY nz_lit) cfml ∧
  check_lrups_unsat lrups (build_cfml cid (conv_cfml cfml)) ⇒
  unsatisfiable_cnf (set cfml)
Proof
  strip_tac>>
  drule check_lrups_unsat_sound>>
  simp[unsatisfiable_cnf_def,satisfiable_cnf_def]>>
  metis_tac[conv_cfml_sound]
QED

(***
  Parser for the compressed LRUP format.

  Records are variable-byte encoded and terminated by a zero byte. A
  deletion is one record, a RUP step is two:

    d <ids> 0
    a <id> <clause> 0    <hints> 0
 ***)

Definition parse_lrup_chunk_def:
  parse_lrup_chunk s =
  if strlen s = 0 then NONE
  else
  let c = strsub s 0 in
  if c = #"d"
  then SOME (INL (Delvb s))
  else if c = #"a"
  then
    let len = strlen s in
    let (m,i) = parse_vb_num s 1 len in
    if m = 0 ∨ m MOD 2 ≠ 0
    then NONE
    else SOME (INR (m DIV 2, Vector (parse_vb_ilits s i len [])))
  else NONE
End

(* One record's worth of lines: NONE on a parse failure, SOME NONE at
  end of file, and otherwise the step together with the unread lines *)
Definition parse_lrup_one_def:
  parse_lrup_one lines =
  case lines of
    [] => SOME NONE
  | l::ls =>
    (case parse_lrup_chunk l of
      NONE => NONE
    | SOME (INL step) => SOME (SOME (step, ls))
    | SOME (INR (id,cl)) =>
      (case ls of
        [] => NONE
      | h::rest => SOME (SOME (Lrupvb id cl h, rest))))
End

Theorem parse_lrup_one_LENGTH:
  parse_lrup_one lines = SOME (SOME (step,rest)) ⇒
  LENGTH rest < LENGTH lines
Proof
  rw[parse_lrup_one_def]>>
  gvs[AllCaseEqs()]
QED

Definition parse_lrups_def:
  parse_lrups lines =
  case parse_lrup_one lines of
    NONE => NONE
  | SOME NONE => SOME []
  | SOME (SOME (step,rest)) =>
    (case parse_lrups rest of
      NONE => NONE
    | SOME ss => SOME (step :: ss))
Termination
  WF_REL_TAC` measure LENGTH`>>
  rw[]>>
  drule parse_lrup_one_LENGTH>>
  simp[]
End
