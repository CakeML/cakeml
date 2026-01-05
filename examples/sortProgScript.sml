(*
  Program to sort the lines in a file, built on top of the quick sort example.
*)
Theory sortProg
Ancestors
  quicksortProg cfApp basis_ffi
Libs
  preamble basis

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = translation_extends"quicksortProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* TODO: move *)
Theorem perm_zip:
   !l1 l2 l3 l4.
    LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1,l2)) (ZIP (l3,l4))
    ⇒
    PERM l1 l3 ∧ PERM l2 l4
Proof
  rw [] >>
  metis_tac [MAP_ZIP, PERM_MAP]
QED

Theorem list_type_v_to_list:
   !A l v.
    LIST_TYPE A l v ⇒
    ?l'. v_to_list v = SOME l' ∧ LIST_REL A l l'
Proof
  Induct_on `l` >>
  rw [LIST_TYPE_def, semanticPrimitivesTheory.v_to_list_def]
  >- EVAL_TAC >>
  rw [semanticPrimitivesTheory.v_to_list_def] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  rw [] >> EVAL_TAC
QED

Theorem string_list_uniq:
   !l1 l2.
    LIST_REL STRING_TYPE l1 l2 ⇒ l2 = MAP (λs. Litv (StrLit (explode s))) l1
Proof
  Induct_on `l1` >>
  rw [] >>
  `?s'. h = strlit s'` by metis_tac [mlstringTheory.mlstring_nchotomy] >>
  fs [STRING_TYPE_def]
QED

Theorem string_not_lt:
   ¬(x < y) ⇔ (y:string) ≤ x
Proof
  rw[string_le_def]
  \\ metis_tac[string_lt_total,string_lt_antisym]
QED

Theorem strict_weak_order_string_cmp:
   strict_weak_order (λs1 s2. explode s1 < explode s2)
Proof
  rw [strict_weak_order_alt, transitive_def] >>
  metis_tac [string_lt_antisym, string_lt_trans, string_lt_total]
QED

Theorem string_le_transitive:
   transitive string_le
Proof
  rw[transitive_def,string_le_def]
  \\ metis_tac[string_lt_trans]
QED

Theorem string_le_antisymmetric:
   antisymmetric string_le
Proof
  rw[antisymmetric_def,string_le_def]
  \\ metis_tac[string_lt_antisym]
QED

Theorem SORTED_string_lt_le:
   SORTED string_lt ls ⇒ SORTED string_le ls
Proof
  strip_tac \\ match_mp_tac SORTED_weaken
  \\ asm_exists_tac \\ rw[string_le_def]
QED

Theorem validArg_filename:
   validArg x ∧ STRING_TYPE x v ⇒ FILENAME x v
Proof
  rw [validArg_def, FILENAME_def, EVERY_MEM, LENGTH_explode]
QED

Theorem validArg_filename_list:
   !x v. EVERY validArg x ∧ LIST_TYPE STRING_TYPE x v ⇒ LIST_TYPE FILENAME x v
Proof
  Induct_on `x` >>
  rw [LIST_TYPE_def, validArg_filename]
QED

Definition v_to_string_def:
  v_to_string (Litv (StrLit s)) = s
End

Theorem LIST_REL_STRING_TYPE:
   LIST_REL STRING_TYPE ls vs ⇒ ls = MAP (implode o v_to_string) vs
Proof
  rw[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP] \\ rfs[] \\ res_tac \\
  Cases_on`EL x ls` \\ fs[STRING_TYPE_def,v_to_string_def,implode_def]
QED
(* -- *)

Definition usage_string_def:
  usage_string = strlit"Usage: sort <file> <file>...\n"
End

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

Quote add_cakeml:
  fun get_files_contents files acc =
    case files of
      [] => Some acc
    | file::files =>
      case TextIO.inputLinesFile #"\n" file of
        None => None
      | Some res => get_files_contents files (res @ acc);
End

Theorem get_files_contents_spec:
   !fnames_v fnames acc_v acc fs.
    hasFreeFD fs ∧
    LIST_TYPE FILENAME fnames fnames_v ∧
    LIST_TYPE STRING_TYPE acc acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_files_contents" (get_ml_prog_state ()))
      [fnames_v; acc_v]
      (STDIO fs)
      (POSTv v.
        STDIO fs *
        &(
        OPTION_TYPE (LIST_TYPE STRING_TYPE)
          if EVERY (inFS_fname fs) fnames
          then
            SOME (FLAT (REVERSE (MAP (all_lines_file fs) fnames))
              ++ acc)
          else
             NONE) v)
Proof
  Induct_on `fnames` >>
  rpt gen_tac>> strip_tac>>
  xcf "get_files_contents" (get_ml_prog_state ())
  \\ fs [LIST_TYPE_def]
  \\ xmatch
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def])>>
  xlet_autop>>
  pop_assum mp_tac>>
  IF_CASES_TAC>>
  simp[OPTION_TYPE_def]>>
  strip_tac>>
  xmatch
  >- (
    xlet_autop>>
    xapp>>
    simp[]>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl>>rw[])>>
  xcon>>xsimpl
QED

Quote add_cakeml:
  fun get_contents args =
    case args of
      [] => Some (TextIO.inputLinesStdIn #"\n")
    | files => get_files_contents files []
End

Definition good_args_def:
  good_args fs fnames ⇔
  fnames = [] ∨
  EVERY (inFS_fname fs) fnames
End

Theorem get_contents_spec:
  (if fnames = [] then
    ∃text. stdin_content fs = SOME text
  else
    hasFreeFD fs) ∧
  LIST_TYPE FILENAME fnames fnames_v
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_contents" (get_ml_prog_state ()))
    [fnames_v]
    (STDIO fs)
    (POSTv v.
      SEP_EXISTS fss.
      STDIO fss *
      &(
        OPTION_TYPE (LIST_TYPE STRING_TYPE)
          (
            if good_args fs fnames
            then
              SOME
                (
                  if fnames = []
                  then
                    (lines_of (implode (THE (stdin_content fs ))))
                  else
                    (FLAT (REVERSE (MAP (all_lines_file fs) fnames)))
                )
            else
              NONE
          ) v ∧
          if fnames = []
          then fss = fastForwardFD fs 0
          else fss = fs
        ))
Proof
  strip_tac>>
  xcf "get_contents" (get_ml_prog_state ())
  \\ Cases_on`fnames`>>gvs[LIST_TYPE_def]
  \\ xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    rw[good_args_def]>>
    fs[OPTION_TYPE_def,lines_of_gen_lines_of])>>
  reverse(rw[good_args_def])
  >- (
    xlet_autop>>xapp>>
    xsimpl>>
    qexists_tac`emp`>>
    qexists_tac`fs`>>
    qexists_tac`h::t`>>
    qexists_tac`[]`>>xsimpl>>
    rw[LIST_TYPE_def,good_args_def,OPTION_TYPE_def])>>
  xlet_autop>>
  xapp>>xsimpl>>
  qexists_tac`emp`>>
  qexists_tac`fs`>>
  qexists_tac`h::t`>>
  qexists_tac`[]`>>xsimpl>>
  rw[LIST_TYPE_def,good_args_def,OPTION_TYPE_def]
QED

Quote add_cakeml:
  fun sort () =
    case
      get_contents (CommandLine.arguments ()) of
      None =>
        TextIO.output TextIO.stdErr "Cannot open file"
    | Some contents_list =>
    let
      val contents_array = Array.fromList contents_list
    in
      (quicksort String.< contents_array;
       Array.app TextIO.print contents_array)
    end
End

Definition valid_sort_result_def:
  valid_sort_result cl init_fs result_fs ⇔
    if good_args init_fs (TL cl) then
      let (lines, fs) =
        if TL cl = [] then
          (lines_of (implode (THE (stdin_content init_fs))),
           fastForwardFD init_fs 0)
        else
          (FLAT (MAP (all_lines_file init_fs) (TL cl)), init_fs)
      in
        ∃output.
        PERM output lines ∧
        SORTED mlstring_le output ∧
        result_fs = add_stdout fs (concat output)
    else result_fs = add_stderr init_fs (strlit "Cannot open file")
End

Theorem valid_sort_result_unique:
   valid_sort_result cl fs fs1 ∧
   valid_sort_result cl fs fs2 ⇒
   fs1 = fs2
Proof
  rw[valid_sort_result_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ match_mp_tac (MP_CANON SORTED_PERM_EQ)
  \\ instantiate
  \\ simp[transitive_mlstring_le,antisymmetric_mlstring_le]
  \\ metis_tac[PERM_SYM,PERM_TRANS]
QED

Theorem valid_sort_result_exists:
   ∃r. valid_sort_result cl fs r
Proof
  rw[valid_sort_result_def]
  \\ TRY CASE_TAC
  \\ PROVE_TAC[QSORT_SORTED, QSORT_PERM, PERM_SYM, total_def,
               total_mlstring_le, transitive_mlstring_le ]
QED

Theorem valid_sort_result_numchars:
   valid_sort_result cl fs1 fs2 ⇒ fs2.numchars = fs1.numchars
Proof
  rw[valid_sort_result_def] \\ rw[]
QED

val sort_sem_def = new_specification("sort_sem_def",["sort_sem"],
  valid_sort_result_exists
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM]);

Theorem sort_sem_intro:
   (∀out. valid_sort_result cl fs out ⇒ P out)
   ⇒ P (sort_sem cl fs)
Proof
  metis_tac[sort_sem_def,valid_sort_result_unique]
QED

Theorem sort_sem_numchars[simp]:
   (sort_sem cl fs).numchars = fs.numchars
Proof
  DEEP_INTRO_TAC sort_sem_intro
  \\ metis_tac[valid_sort_result_numchars]
QED

Theorem SORTED_mlstring_le[local]:
    !output. SORTED mlstring_le output = SORTED $<= (MAP explode output)
Proof
  Induct \\ fs [SORTED_DEF]
  \\ Cases_on `output` \\ fs [SORTED_DEF]
  \\ Cases \\ Cases_on `h`
  \\ fs [explode_def,strlit_le_strlit]
QED

Theorem sort_spec:
   (if LENGTH cl ≤ 1
    then ∃text. stdin_content fs = SOME text
    else hasFreeFD fs)
    ⇒
    app (p : 'ffi ffi_proj) ^(fetch_v "sort" (get_ml_prog_state ()))
      [Conv NONE []]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
        &UNIT_TYPE () uv *
          STDIO (sort_sem cl fs) * COMMANDLINE cl)
Proof
  strip_tac >>
  xcf "sort" (get_ml_prog_state ()) >>
  xmatch >>
  rpt xlet_autop>>
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) >>
  fs[wfcl_def] >>
  qabbrev_tac `fnames = TL cl` >>
  `(if fnames = [] then
    ∃text. stdin_content fs = SOME text
  else
    hasFreeFD fs)` by (
      Cases_on`cl`>>gvs[]>>
      every_case_tac>>gvs[ADD1,NOT_NIL_EQ_LENGTH_NOT_0])>>
  `LIST_TYPE FILENAME fnames argv` by (
    drule_then irule LIST_TYPE_mono>>
    rw[FILENAME_def]>>
    fs[Abbr`fnames`,EVERY_MEM]>>
    Cases_on`cl`>>fs[validArg_def])>>
  drule_all get_contents_spec>>
  strip_tac>>
  xlet_auto
  >- (xsimpl>>rw[]>>xsimpl)>>
  gvs[]>>
  reverse (Cases_on`good_args fs fnames`)>>
  gvs[OPTION_TYPE_def]>>xmatch
  >- (
    xapp_spec output_stderr_spec >>
    xsimpl >>
    DEEP_INTRO_TAC sort_sem_intro >>
    simp[valid_sort_result_def] \\
    gvs[good_args_def]>>
    xsimpl>>
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`fs` \\
    xsimpl ) \\
  qmatch_assum_abbrev_tac `LIST_TYPE STRING_TYPE strings strings_v` >>
  imp_res_tac list_type_v_to_list \\
  (* TODO: This let should be solvable by xlet_auto *)
  xlet
    `POSTv v. ARRAY v l' * COMMANDLINE cl *
              STDIO fss`
  >- (
    drule array_fromList_spec
    \\ disch_then drule \\ strip_tac
    \\ xapp \\ xsimpl
  ) \\
  assume_tac strict_weak_order_string_cmp \\
  xlet_auto >- (
    xsimpl
    \\ mp_tac StringProgTheory.mlstring_lt_v_thm
    \\ simp[mlstringTheory.mlstring_lt_inv_image,inv_image_def] )
  \\ xapp >>
  xsimpl >>
  qexists_tac `COMMANDLINE cl` >>
  xsimpl >>
  qexists_tac `\l n. STDIO (add_stdout fss (implode (CONCAT (MAP v_to_string (TAKE n l)))))` >>
  xsimpl >>
  simp [implode_def] >>
  DEP_REWRITE_TAC[GEN_ALL add_stdo_nil] >>
  conj_asm1_tac
  >- (
    Cases_on`fnames = []` \\ gvs[]
    \\ imp_res_tac STD_streams_stdout
    \\ rw[stdo_fastForwardFD]
    \\ asm_exists_tac \\ rw[] ) >>
  xsimpl \\
  rw []
  >- (
    xapp >>
    xsimpl >>
    simp [MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF, v_to_string_def] >>
    qexists_tac `emp` >>
    xsimpl >>
    qmatch_goalsub_rename_tac`EL n sorted_vs` \\
    qmatch_assum_rename_tac`LIST_REL STRING_TYPE sorted sorted_vs` \\
    qexists_tac `EL n sorted` >>
    qmatch_goalsub_abbrev_tac`STDIO fs'` \\
    qexists_tac`fs'` \\
    simp [ETA_THM, EL_MAP] >>
    xsimpl >>
    conj_asm1_tac
    >- metis_tac [LIST_REL_EL_EQN] >>
    rw [TAKE_EL_SNOC, EL_MAP, SNOC_APPEND, Abbr`fs'`] >>
    DEP_REWRITE_TAC[GEN_ALL add_stdo_o] >>
    conj_tac >- metis_tac[] >>
    Cases_on`EL n sorted` \\ fs[STRING_TYPE_def,v_to_string_def] \\
    fs [strcat_def,concat_def] \\
    xsimpl)
  >- (
    DEEP_INTRO_TAC sort_sem_intro \\
    rw[valid_sort_result_def] \\
    qmatch_abbrev_tac`STDIO (add_stdout _ s1) * _ ==>> STDIO (add_stdout _ s2) *_` \\
    gvs[add_stdo_def] >>
    `s1 = s2` suffices_by xsimpl \\
    simp[Abbr`s1`,Abbr`s2`] \\
    simp [concat_def] \\
    AP_TERM_TAC \\
    drule PERM_ZIP \\
    imp_res_tac LIST_REL_LENGTH \\
    disch_then(last_assum o mp_then (Pos (el 3)) mp_tac) \\ simp[] \\
    disch_then(first_assum o mp_then (Pos (el 2)) mp_tac) \\ simp[] \\
    qmatch_assum_abbrev_tac`PERM output orig` \\
    `PERM orig strings` by
      simp[Abbr`orig`,Abbr`strings`,PERM_FLAT] \\
    fs[Abbr`orig`] \\ strip_tac \\
    match_mp_tac (MP_CANON SORTED_PERM_EQ) \\
    qexists_tac `string_le` \\
    simp[string_le_transitive,string_le_antisymmetric] \\
    fs[GSYM inv_image_def,string_not_lt] \\
    fs[GSYM sorted_map,string_le_transitive] \\
    imp_res_tac LIST_REL_STRING_TYPE \\ rveq \\
    fs[MAP_MAP_o,o_DEF,ETA_AX] \\
    `(λs. case s of strlit x => x) = explode` by
          (fs [FUN_EQ_THM] \\ Cases \\ fs []) \\ fs [] \\
    fs [SORTED_mlstring_le] \\
    drule (Q.ISPEC `explode `PERM_MAP) \\
    fs [MAP_MAP_o,o_DEF] \\
    CONV_TAC (DEPTH_CONV ETA_CONV) \\
    strip_tac \\
    match_mp_tac PERM_TRANS \\
    asm_exists_tac \\ fs [] \\
    qpat_x_assum `PERM output _` assume_tac \\
    once_rewrite_tac [PERM_SYM] \\
    drule (Q.ISPEC `explode `PERM_MAP) \\
    fs [MAP_MAP_o,o_DEF] \\
    CONV_TAC (DEPTH_CONV ETA_CONV) \\
    fs [] \\
    qpat_x_assum `PERM (FLAT _) (MAP _ _)` assume_tac \\
    drule (Q.ISPEC `explode `PERM_MAP) \\
    fs [MAP_MAP_o,o_DEF] \\
    metis_tac[PERM_TRANS]
    )
QED

Theorem sort_whole_prog_spec:
   (if LENGTH cl ≤ 1 then (∃input. get_file_content fs 0 = SOME (input,0)) else hasFreeFD fs)
   ⇒ whole_prog_spec ^(fetch_v "sort" (get_ml_prog_state())) cl fs NONE (valid_sort_result cl fs)
Proof
  disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qexists_tac`sort_sem cl fs`
  \\ reverse conj_tac
  >- metis_tac[with_same_numchars,sort_sem_numchars,sort_sem_def]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH sort_spec)))
  \\ xsimpl
QED

val (sem_thm,prog_tm) = whole_prog_thm (get_ml_prog_state ()) "sort" (UNDISCH sort_whole_prog_spec)
Definition sort_prog_def:
  sort_prog = ^prog_tm
End

Theorem sort_semantics =
  sem_thm |> ONCE_REWRITE_RULE[GSYM sort_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
