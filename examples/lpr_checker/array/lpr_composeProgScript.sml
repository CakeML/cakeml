(*
  Define and verify LPR composition checker function
*)
open preamble basis md5ProgTheory cfLib basisFunctionsLib;

val _ = new_theory "lpr_composeProg"

val _ = translation_extends "md5Prog";

Definition next_nondigit_def:
  next_nondigit i s =
    if i < strlen s then
      let c = strsub s i in
        if ORD #"0" ≤ ORD c ∧ ORD c ≤ ORD #"9"
        then next_nondigit (i+1:num) s else i
    else i
Termination
  WF_REL_TAC ‘measure (λ(i,s). strlen s - i:num)’
End

val res = translate next_nondigit_def;

Definition get_ranges_def:
  get_ranges prefix [] = INR [] ∧
  get_ranges prefix (line::lines) =
    if ~(mlstring$isPrefix prefix line) then
      INL (strlit"ERROR: Incorrect prefix on line: " ^ line ^ strlit"\n")
    else
      let i0 = strlen prefix in
      let i1 = next_nondigit i0 line in
      let j0 = i1 + 2 in
      let j1 = next_nondigit j0 line in
        if j1 ≠ strlen line ∨ i0 = i1 ∨ j0 = j1 then
          INL (strlit "ERROR: Bad ranges on line: " ^ line)
        else
        if strsub line i1 ≠ #"-" ∨ strsub line (i1+1) ≠ #"-" then
          INL (strlit "ERROR: Missing -- on line: " ^ line)
        else
          case get_ranges prefix lines of
          | INL err => INL err
          | INR xs => INR ((fromNatString (substring line i0 (i1-i0)),
                            fromNatString (substring line j0 (j1-j0)))::xs)
End

val res = translate get_ranges_def;

Theorem get_ranges_side:
  ∀prefix lines. get_ranges_side prefix lines = T
Proof
  Induct_on ‘lines’ \\ rw []
  \\ once_rewrite_tac [fetch "-" "get_ranges_side_def"]
  \\ fs [] \\ rw []
  \\ cheat
QED

val _ = update_precondition get_ranges_side;

Definition expected_prefix_def:
  expected_prefix cnf_fname cnf_md5 proof_fname proof_md5 =
    concat [cnf_fname; strlit " ";
            cnf_md5; strlit " ";
            proof_fname; strlit " ";
            proof_md5; strlit " "]
End

val res = translate expected_prefix_def;

Definition check_lines_def:
  check_lines cnf_fname cnf_md5 proof_fname proof_md5 lines =
    let prefix = expected_prefix cnf_fname cnf_md5 proof_fname proof_md5 in
      case get_ranges prefix lines of
      | INL err => err
      | INR ranges => strlit "not implemented yet"
End

val res = translate check_lines_def;

val _ = (append_prog o process_topdecs) `
  fun check_compose cnf_fname proof_fname lines_fname =
    case md5_of (Some cnf_fname) of
      None => print ("ERROR: cannot read CNF file " ^ cnf_fname ^ "\n")
    | Some cnf_md5 =>
      case md5_of (Some proof_fname) of
        None => print ("ERROR: cannot read proof file " ^ proof_fname ^ "\n")
      | Some proof_md5 =>
        case TextIO.b_inputLinesFrom lines_fname of
          None => print ("ERROR: cannot read lines file " ^ lines_fname ^ "\n")
        | Some lines => print (check_lines cnf_fname cnf_md5 proof_fname proof_md5 lines)`;

Theorem check_compose_spec:
  FILENAME cnf_fname cnfv     ∧ file_content fs cnf_fname = SOME cnf ∧
  FILENAME proof_fname proofv ∧ file_content fs proof_fname = SOME proof ∧
  FILENAME lines_fname linesv ∧ file_content fs lines_fname = SOME x ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) check_compose_v [cnfv; proofv; linesv]
    (STDIO fs)
    (POSTv retv.
      STDIO (add_stdout fs
        (check_lines cnf_fname (implode (md5 cnf))
                     proof_fname (implode (md5 proof))
                     (lines_of (strlit x)))) *
      & (UNIT_TYPE () retv))
Proof
  rpt strip_tac
  \\ xcf_with_def "check_compose" (fetch "-" "check_compose_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ rw []
  \\ xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs cnf_fname)) retv)’
  THEN1 (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ rw []
  \\ xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs proof_fname)) retv)’
  THEN1 (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (SOME (lines_of (strlit x))) retv)’
  THEN1 (xapp_spec b_inputLinesFrom_spec \\ fs []
         \\ first_assum $ irule_at (Pos hd) \\ fs []
         \\ first_assum $ irule_at (Pos hd) \\ fs []
         \\ xsimpl
         \\ fs [file_content_def,AllCaseEqs(),inFS_fname_def,all_lines_def]
         \\ fs [std_preludeTheory.OPTION_TYPE_def,implode_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def,implode_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xapp
  \\ xsimpl
  \\ first_assum $ irule_at (Pos hd) \\ fs []
  \\ qexists_tac ‘fs’
  \\ xsimpl
QED

val _ = export_theory();
