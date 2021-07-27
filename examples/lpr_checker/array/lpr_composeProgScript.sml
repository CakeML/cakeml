(*
  Define and verify LPR composition checker function
*)
open preamble basis md5ProgTheory cfLib basisFunctionsLib spt_closureTheory;

val _ = new_theory "lpr_composeProg"

val _ = translation_extends "md5Prog";

(* TODO: move *)

Definition interval_cover_def:
  (interval_cover i j [] ⇔ i = j) ∧
  (interval_cover (i:num) j ((a,b)::xs) ⇔ a = i ∧ interval_cover b j xs)
End

(* / TODO *)

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

Definition get_num_acc_def:
  get_num_acc [] k = (k,[],T) ∧
  get_num_acc (c::cs) k =
    if ORD #"0" ≤ ORD c ∧ ORD c ≤ ORD #"9" then
      get_num_acc cs (k * 10 + (ORD c - ORD #"0"))
    else (k,c::cs,T)
End

Definition get_num_def:
  get_num [] = (0,[],F) ∧
  get_num (c::cs) =
    if ORD #"0" ≤ ORD c ∧ ORD c ≤ ORD #"9" then
      if c = #"0" then (0,cs,T)
      else get_num_acc (c::cs) 0
    else (0,c::cs,F)
End

Definition get_chr_def:
  get_chr c [] = ([],F) ∧
  get_chr c (x::xs) = (xs,x = (c:char))
End

Definition get_range_def:
  get_range prefix line =
    if ~(mlstring$isPrefix prefix line) then
      INL (strlit"ERROR: Incorrect prefix on line: " ^ line ^ strlit"\n")
    else
      let i = strlen prefix in
      let l = strlen line in
      let xs = explode (substring line i (l-i)) in
      let (n,xs,b1) = get_num xs in
      let (xs,b2) = get_chr #"-" xs in
      let (xs,b3) = get_chr #"-" xs in
      let (m,xs,b4) = get_num xs in
      let (xs,b5) = get_chr #"\n" xs in
      let g = (b1 ∧ b2 ∧ b3 ∧ b4 ∧ b5 ∧ NULL xs) in
        if g then INR (n,m)
        else INL (strlit "ERROR: Bad ranges on line: " ^ line)
End

val res = translate get_num_acc_def;
val res = translate get_num_def;
val res = translate get_chr_def;
val res = translate get_range_def;

Theorem get_range_side:
  get_range_side x y = T
Proof
  fs [fetch "-" "get_range_side_def"]
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs [isPrefix_def]
QED

val _ = update_precondition get_range_side;

Definition get_ranges_def:
  get_ranges prefix [] = INR [] ∧
  get_ranges prefix (line::lines) =
    case get_range prefix line of
    | INL err => INL err
    | INR y =>
      case get_ranges prefix lines of
      | INL err => INL err
      | INR ys => INR (y::ys)
End

val res = translate get_ranges_def;

Definition expected_prefix_def:
  expected_prefix cnf_fname cnf_md5 proof_fname proof_md5 =
    concat [cnf_fname; strlit " ";
            cnf_md5; strlit " ";
            proof_fname; strlit " ";
            proof_md5; strlit " "]
End

val res = translate expected_prefix_def;

Definition build_sets_def:
  build_sets [] acc = acc ∧
  build_sets ((n,m)::rest) acc =
    let s = (case lookup n acc of NONE => LN | SOME s => s) in
      build_sets rest (insert n (insert m () s) acc)
End

val res = translate lookup_def;
val res = translate insert_def;
val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate inter_def;
val res = translate union_def;
val res = translate spt_center_def;
val res = translate spt_left_def;
val res = translate spt_right_def;
val res = translate subspt_eq;
val res = translate spt_fold_def;
val res = translate closure_spt_def;
val res = translate build_sets_def;

Definition check_lines_def:
  check_lines cnf_fname cnf_md5 proof_fname proof_md5 lines (n:num) =
    let prefix = expected_prefix cnf_fname cnf_md5 proof_fname proof_md5 in
      case get_ranges prefix lines of
      | INL err => err
      | INR ranges =>
        let start = insert 0 () LN in
        let r = closure_spt start (build_sets ranges LN) in
          case lookup n r of
          | NONE =>
              concat [strlit "ERROR: intervals do not reach "; toString n; strlit "\n"]
          | SOME u =>
              concat [strlit "OK: intervals covered "; toString n; strlit "\n"]
End

val res = translate check_lines_def;

Definition add_one_def:
  add_one (n:mlstring) m = m+1:num
End

val add_one_v = translate add_one_def;

val _ = (append_prog o process_topdecs) `
  fun line_count_of fname =
    TextIO.foldLines add_one 0 (Some fname)`;

Theorem line_count_of_spec:
  FILENAME proof_fname proofv ∧ file_content fs proof_fname = SOME proof ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) line_count_of_v [proofv]
    (STDIO fs)
    (POSTv retv. STDIO fs *
      & (OPTION_TYPE NUM (SOME (LENGTH (lines_of (strlit proof)))) retv))
Proof
  rpt strip_tac
  \\ xcf_with_def "line_count_of" (fetch "-" "line_count_of_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ assume_tac add_one_v
  \\ drule TextIOProofTheory.foldLines_SOME
  \\ strip_tac
  \\ xapp
  \\ first_x_assum $ irule_at $ Pos hd
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ first_x_assum $ irule_at $ Pos hd
  \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,implode_def]
  \\ rw []
  \\ qsuff_tac ‘∀xs n. foldl add_one n xs = LENGTH xs + n’
  THEN1 (rw [] \\ gvs [])
  \\ Induct \\ fs [mllistTheory.foldl_def,add_one_def,ADD1]
QED

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
        | Some lines =>
          case line_count_of proof_fname of
            None => print ("ERROR: cannot read proof file " ^ proof_fname ^ "\n")
          | Some n =>
              print (check_lines cnf_fname cnf_md5 proof_fname proof_md5 lines n)`;

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
                     (lines_of (strlit x))
                     (LENGTH (lines_of (strlit proof))))) *
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
  \\ qpat_x_assum ‘file_content fs proof_fname = SOME proof’ assume_tac
  \\ drule_at (Pos $ el 2) line_count_of_spec
  \\ disch_then drule
  \\ disch_then (qspec_then ‘p’ assume_tac)
  \\ gvs []
  \\ xlet_auto THEN1 xsimpl
  \\ fs [std_preludeTheory.OPTION_TYPE_def,implode_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xapp
  \\ xsimpl
  \\ first_assum $ irule_at (Pos hd) \\ fs []
  \\ qexists_tac ‘fs’
  \\ xsimpl
QED

Theorem check_compose_spec_fail:
  FILENAME cnf_fname cnfv     ∧
  FILENAME proof_fname proofv ∧
  FILENAME lines_fname linesv ∧
  MEM NONE [file_content fs cnf_fname;
            file_content fs proof_fname;
            file_content fs lines_fname] ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) check_compose_v [cnfv; proofv; linesv]
    (STDIO fs)
    (POSTv retv.
      SEP_EXISTS output.
        STDIO (add_stdout fs output) * & (isPrefix (strlit "ERROR") output))
Proof
  rpt strip_tac
  \\ xcf_with_def "check_compose" (fetch "-" "check_compose_v_def")
  \\ reverse (Cases_on ‘STD_streams fs’)
  THEN1 (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on ‘consistentFS fs’)
  THEN1
    (fs [STDIO_def,IOFS_def,wfFS_def] \\ xpull
     \\ fs [fsFFIPropsTheory.consistentFS_def]
     \\ res_tac \\ fs [])
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ rw []
  \\ xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs cnf_fname)) retv)’
  THEN1 (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ Cases_on ‘file_content fs cnf_fname’
  THEN1
   (fs []
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch
    \\ xlet_auto THEN1 xsimpl
    \\ xlet_auto THEN1 xsimpl
    \\ xapp
    \\ xsimpl
    \\ first_assum $ irule_at (Pos hd) \\ fs []
    \\ qexists_tac ‘fs’ \\ xsimpl
    \\ rw []
    \\ qmatch_goalsub_abbrev_tac ‘ss ^ tt’
    \\ qexists_tac ‘ss ^ tt’
    \\ xsimpl \\ unabbrev_all_tac \\ EVAL_TAC \\ fs [] \\ EVAL_TAC)
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp [std_preludeTheory.OPTION_TYPE_def] \\ rw []
  \\ xmatch
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ rw []
  \\ xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs proof_fname)) retv)’
  THEN1 (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ Cases_on ‘file_content fs proof_fname’
  THEN1
   (fs []
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch
    \\ xlet_auto THEN1 xsimpl
    \\ xlet_auto THEN1 xsimpl
    \\ xapp
    \\ xsimpl
    \\ first_assum $ irule_at (Pos hd) \\ fs []
    \\ qexists_tac ‘fs’ \\ xsimpl
    \\ rw []
    \\ qmatch_goalsub_abbrev_tac ‘ss ^ tt’
    \\ qexists_tac ‘ss ^ tt’
    \\ xsimpl \\ unabbrev_all_tac \\ EVAL_TAC \\ fs [] \\ EVAL_TAC)
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp [std_preludeTheory.OPTION_TYPE_def] \\ rw []
  \\ xmatch
  \\ xlet ‘(POSTv retv.
             STDIO fs * &OPTION_TYPE (LIST_TYPE STRING_TYPE) NONE retv)’
  THEN1 (xapp_spec b_inputLinesFrom_spec \\ fs []
         \\ first_assum $ irule_at (Pos hd) \\ fs []
         \\ first_assum $ irule_at (Pos hd) \\ fs []
         \\ xsimpl
         \\ fs [inFS_fname_def,file_content_def]
         \\ gvs [consistentFS_def,AllCaseEqs()]
         \\ res_tac
         \\ fs []
         \\ imp_res_tac ALOOKUP_NONE)
  \\ fs [std_preludeTheory.OPTION_TYPE_def,implode_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 xsimpl
  \\ xapp
  \\ xsimpl
  \\ first_assum $ irule_at (Pos hd) \\ fs []
  \\ qexists_tac ‘fs’ \\ xsimpl
  \\ rw []
  \\ qmatch_goalsub_abbrev_tac ‘ss ^ tt’
  \\ qexists_tac ‘ss ^ tt’
  \\ xsimpl \\ unabbrev_all_tac \\ EVAL_TAC \\ fs [] \\ EVAL_TAC
QED

Theorem is_adjacent_build_sets:
  ∀xs t m n.
    is_adjacent (build_sets xs t) m n ⇔
    MEM (m,n) xs ∨ is_adjacent t m n
Proof
  Induct \\ fs [build_sets_def,FORALL_PROD]
  \\ rw [] \\ Cases_on ‘MEM (m,n) xs’ \\ fs []
  \\ CASE_TAC \\ rw []
  \\ simp [is_adjacent_def,lookup_insert]
  \\ IF_CASES_TAC \\ gvs [lookup_insert,lookup_def]
  \\ IF_CASES_TAC \\ gvs [lookup_insert,lookup_def]
QED

Theorem is_adjacent_build_sets:
  is_adjacent (build_sets xs LN) m n = MEM (m,n) xs
Proof
  fs [is_adjacent_build_sets]
  \\ fs [is_adjacent_def,lookup_def]
QED

Theorem is_reachable_build_sets:
  is_reachable (build_sets xs LN) n m ⇔
  ∃path. interval_cover n m path ∧ set path ⊆ set xs
Proof
  eq_tac \\ fs [is_reachable_def]
  THEN1
   (qid_spec_tac ‘m’ \\ qid_spec_tac ‘n’
    \\ ho_match_mp_tac RTC_INDUCT \\ rw []
    THEN1 (qexists_tac ‘[]’ \\ fs [interval_cover_def])
    \\ rename [‘is_adjacent _ n k’]
    \\ qexists_tac ‘(n,k)::path’
    \\ fs [interval_cover_def, is_adjacent_build_sets])
  \\ fs [PULL_EXISTS]
  \\ qid_spec_tac ‘m’ \\ qid_spec_tac ‘n’
  \\ Induct_on ‘path’
  \\ fs [interval_cover_def,FORALL_PROD] \\ rw []
  \\ irule (RTC_rules |> SPEC_ALL |> CONJUNCT2)
  \\ qexists_tac ‘p_2’ \\ fs [is_adjacent_build_sets]
QED

Theorem get_ranges_IML_IMP:
  ∀lines prefix. get_ranges prefix lines = INL x ⇒ isPrefix «ERROR» x
Proof
  Induct \\ fs [get_ranges_def,AllCaseEqs()]
  \\ rw [] \\ res_tac \\ fs []
  \\ gvs [get_range_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ EVAL_TAC \\ fs [] \\ EVAL_TAC
QED

Theorem check_lines_correct:
  ~isPrefix (strlit "ERROR")
            (check_lines cnf_fname cnf_md5 proof_fname proof_md5 lines n)
  ⇒
  ∃path ranges.
    interval_cover 0 n path ∧ set path ⊆ set ranges ∧
    get_ranges (expected_prefix cnf_fname cnf_md5 proof_fname proof_md5)
      lines = INR ranges
Proof
  fs [check_lines_def] \\ CASE_TAC
  \\ imp_res_tac get_ranges_IML_IMP
  \\ CASE_TAC \\ fs []
  THEN1 (EVAL_TAC \\ fs [] \\ EVAL_TAC)
  \\ rw []
  \\ fs [GSYM is_reachable_build_sets]
  \\ fs [closure_spt_thm |> SIMP_RULE (srw_ss()) [EXTENSION,domain_lookup]]
  \\ gvs [lookup_insert,lookup_def]
QED

val _ = export_theory();
