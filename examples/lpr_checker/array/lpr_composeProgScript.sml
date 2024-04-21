(*
  Define and verify LPR composition checker function

  The expected line format is:
  s VERIFIED RANGE md5(cnf_file) md5(proof_file) i-j

*)
open preamble basis md5ProgTheory cfLib basisFunctionsLib spt_closureTheory lpr_parsingTheory;

val _ = new_theory "lpr_composeProg"

val _ = translation_extends "md5Prog";

(* TODO: move *)

Theorem isPrefix:
  isPrefix (strlit s) (strlit t) ⇔ s ≼ t
Proof
  fs [isPrefix_def]  \\ fs [isStringThere_aux_def]
  \\ reverse (Cases_on ‘STRLEN s ≤ STRLEN t’)
  THEN1
   (fs [] \\ CCONTR_TAC \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_LENGTH)
  \\ fs []
  \\ qsuff_tac ‘∀x y.
    isStringThere_aux (strlit (x ++ s)) (strlit (y ++ t))
       (LENGTH x) (LENGTH y) (STRLEN s) ⇔ s ≼ t’
  THEN1 (fs [] \\ disch_then (qspecl_then [‘[]’,‘[]’] assume_tac) \\ fs [])
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘s’
  \\ Induct \\ fs [isStringThere_aux_def]
  \\ Cases_on ‘t’ \\ fs [isStringThere_aux_def] \\ rw []
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘x ++ [h']’,‘y ++ [h]’] mp_tac) \\ fs []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND] \\ fs []
  \\ rw [EL_LENGTH_APPEND]
QED

Theorem SEG_LENGTH_APPEND:
  ∀xs ys n. SEG n (LENGTH xs) (xs ++ ys) = SEG n 0 ys
Proof
  Induct \\ Cases_on ‘n’ \\ fs [SEG]
QED

Theorem substring_strcat:
  substring (prefix ^ s) (strlen prefix) n = substring s 0 n
Proof
  Cases_on ‘prefix’ \\ Cases_on ‘s’
  \\ fs [strcat_def,concat_def]
  \\ fs [substring_def,DROP_LENGTH_APPEND]
  \\ fs [DECIDE “n+m ≤ m+k ⇔ n ≤ k:num”]
  \\ rw [SEG_LENGTH_APPEND]
QED

Theorem isPrefix_IMP_append:
  isPrefix prefix h ⇒ ∃s. h = prefix ^ s
Proof
  Cases_on ‘prefix’ \\ Cases_on ‘h’ \\ rw [isPrefix]
  \\ gvs [stringTheory.isPREFIX_STRCAT]
  \\ rename [‘STRCAT s s1’]
  \\ qexists_tac ‘strlit s1’ \\ fs [strcat_def,concat_def]
QED

Theorem substring_TAKE:
  substring (strlit xs) 0 n = strlit (TAKE n xs)
Proof
  rw [substring_def] \\ pop_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘n’
  \\ Induct \\ Cases_on ‘xs’ \\ fs [SEG]
QED

(* -- *)

Definition interval_cover_def:
  (interval_cover i j [] ⇔ i = j) ∧
  (interval_cover (i:num) j ((a,b)::xs) ⇔ a = i ∧ interval_cover b j xs)
End

Theorem interval_cover_satisfiable:
  ∀ijs i j.
  interval_cover i j ijs ∧
  EVERY (λ(i,j).
    (satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
     satisfiable (interp (run_proof fml (TAKE j pf))))) ijs ⇒
  satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
  satisfiable (interp (run_proof fml (TAKE j pf)))
Proof
  Induct>>simp[interval_cover_def,FORALL_PROD]>>rw[]>>fs[]>>
  first_x_assum drule>>
  metis_tac[]
QED

Definition get_range_def:
  get_range prefix line =
    if ~(mlstring$isPrefix prefix line) then
      INL (strlit"c Incorrect prefix on line: " ^ line ^ strlit"\n")
    else
      let i = strlen prefix in
      let l = strlen line in
      if l > 0 ∧ strsub line (l-1) = #"\n" then
        let rest = substring line i (l-i-1) in
        case parse_rng rest of
          NONE => INL (strlit "c Bad ranges on line: " ^ line)
        | SOME (i,j) => INR (i,j)
      else
        INL (strlit "c Bad ranges on line: " ^ line)
End

val _ = translate parse_rng_def;

val parse_rng_side_def = fetch "-" "parse_rng_side_def"

val parse_rng_side = Q.prove(`
  !x. parse_rng_side x ⇔ T`,
  simp[parse_rng_side_def]) |> update_precondition;

val res = translate get_range_def;

Theorem get_range_side:
  get_range_side x y = T
Proof
  fs [fetch "-" "get_range_side_def"]>>
  fs [isPrefix_def]
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
  expected_prefix cnf_md5 proof_md5 =
    concat [strlit "s VERIFIED RANGE ";
            cnf_md5; strlit " ";
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
  check_lines cnf_md5 proof_md5 lines (n:num) =
    let prefix = expected_prefix cnf_md5 proof_md5 in
      case get_ranges prefix lines of
      | INL err => INL err
      | INR ranges =>
        let start = insert 0 () LN in
        let r = closure_spt start (build_sets ranges LN) in
          case lookup n r of
          | NONE =>
              INL (concat [strlit "c Intervals do not reach "; toString n; strlit "\n"])
          | SOME u =>
              INR (concat [strlit "s VERIFIED INTERVALS COVER 0-"; toString n; strlit "\n"])
End

val res = translate check_lines_def;

Definition add_one_def:
  add_one (n:mlstring) m = m+1:num
End

val add_one_v = translate add_one_def;

val _ = (append_prog o process_topdecs) `
  fun line_count_of fname =
    TextIO.foldLines #"\n" add_one 0 (Some fname)`;

(* TODO move? *)
Theorem line_of_gen_lines_of[simp]:
  lines_of_gen #"\n" = lines_of
Proof
  rw[FUN_EQ_THM,lines_of_gen_def,lines_of_def,splitlines_at_def,splitlines_def,str_def]
QED

Theorem all_lines_gen_all_lines[simp]:
  all_lines_gen #"\n" = all_lines
Proof
  rw[FUN_EQ_THM,all_lines_gen_def,all_lines_def]
QED

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
  \\ xcf_with_def (fetch "-" "line_count_of_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ assume_tac add_one_v
  \\ drule_at Any TextIOProofTheory.foldLines_SOME
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

val notfound_string_def = Define`
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]`;

val r = translate notfound_string_def;

val _ = (append_prog o process_topdecs) `
  fun check_compose cnf_fname proof_fname lines_fname =
    case md5_of (Some cnf_fname) of
      None => TextIO.output TextIO.stdErr (notfound_string cnf_fname)
    | Some cnf_md5 =>
      case md5_of (Some proof_fname) of
        None => TextIO.output TextIO.stdErr (notfound_string proof_fname)
      | Some proof_md5 =>
        case TextIO.b_inputLinesFrom #"\n" lines_fname of
          None => TextIO.output TextIO.stdErr (notfound_string lines_fname)
        | Some lines =>
          case line_count_of proof_fname of
            None => TextIO.output TextIO.stdErr (notfound_string proof_fname)
          | Some n =>
              case check_lines cnf_md5 proof_md5 lines n of
                Inl err => TextIO.output TextIO.stdErr err
              | Inr succ => print succ`

Theorem check_compose_spec:
  FILENAME cnf_fname cnfv     ∧ file_content fs cnf_fname = SOME cnf ∧
  FILENAME proof_fname proofv ∧ file_content fs proof_fname = SOME proof ∧
  FILENAME lines_fname linesv ∧ file_content fs lines_fname = SOME x ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) check_compose_v [cnfv; proofv; linesv]
    (STDIO fs)
    (POSTv retv.
      (case check_lines (implode (md5 cnf)) (implode (md5 proof)) (lines_of (strlit x)) (LENGTH (lines_of (strlit proof))) of
        INL err => STDIO (add_stderr fs err)
      | INR out => STDIO (add_stdout fs out)) *
      & (UNIT_TYPE () retv))
Proof
  rpt strip_tac
  \\ xcf_with_def (fetch "-" "check_compose_v_def")
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
  \\ TOP_CASE_TAC \\ fs[SUM_TYPE_def] \\ xmatch
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl)
  \\ xapp
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
      & (UNIT_TYPE () retv) *
      SEP_EXISTS err.
        STDIO (add_stderr fs err))
Proof
  rpt strip_tac
  \\ xcf_with_def (fetch "-" "check_compose_v_def")
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
    \\ xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`notfound_string cnf_fname`>>xsimpl)
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
    \\ xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`notfound_string proof_fname`>>xsimpl)
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
  \\ xapp_spec output_stderr_spec \\ xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>qexists_tac`notfound_string lines_fname`>>xsimpl
QED

Theorem is_adjacent_build_sets_lemma:
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
  fs [is_adjacent_build_sets_lemma]
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

Theorem MEM_get_ranges:
  ∀ls prefix ranges i j.
  get_ranges prefix ls = INR ranges ∧
  MEM (i,j) ranges ⇒
  ∃out. MEM (prefix ^ out ^ strlit"\n") ls ∧ parse_rng out = SOME (i,j)
Proof
  Induct \\ rw[get_ranges_def]
  \\ reverse (gvs[get_range_def,AllCaseEqs()])
  THEN1 metis_tac []
  \\ first_assum (irule_at (Pos last))
  \\ disj1_tac
  \\ imp_res_tac isPrefix_IMP_append \\ gvs []
  \\ fs [substring_strcat]
  \\ rewrite_tac [GSYM strcat_assoc]
  \\ AP_TERM_TAC
  \\ Cases_on ‘s’ \\ Cases_on ‘s'’ using SNOC_CASES
  THEN1
   (rpt (pop_assum mp_tac)
    \\ qid_spec_tac ‘i’
    \\ qid_spec_tac ‘j’
    \\ EVAL_TAC \\ fs [])
  \\ fs [SNOC_APPEND,ADD1,substring_TAKE]
  \\ fs [substring_TAKE,TAKE_LENGTH_APPEND]
  \\ Cases_on ‘prefix’
  \\ fs [strcat_def,concat_def]
  \\ ‘STRLEN l + STRLEN s = STRLEN (STRCAT s l)’ by fs []
  \\ full_simp_tac std_ss [EL_LENGTH_APPEND,NULL,HD] \\ gvs []
QED

Theorem check_lines_correct:
  check_lines cnf_md5 proof_md5 lines n = INR succ
  ⇒
  ∃path ranges.
    interval_cover 0 n path ∧ set path ⊆ set ranges ∧
    get_ranges (expected_prefix cnf_md5 proof_md5)
      lines = INR ranges
Proof
  fs [check_lines_def] \\ CASE_TAC
  \\ CASE_TAC \\ fs []
  \\ rw []
  \\ fs [GSYM is_reachable_build_sets]
  \\ fs [closure_spt_thm |> SIMP_RULE (srw_ss()) [EXTENSION,domain_lookup]]
  \\ gvs [lookup_insert,lookup_def]
QED

val _ = export_theory();
