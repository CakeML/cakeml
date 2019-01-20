(*
  Program to sort the lines in a file, built on top of the quick sort example.
*)

open preamble basis quicksortProgTheory

val _ = new_theory "sortProg";

val _ = translation_extends"quicksortProg";

(* TODO: move *)
Theorem perm_zip
  `!l1 l2 l3 l4.
    LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1,l2)) (ZIP (l3,l4))
    ⇒
    PERM l1 l3 ∧ PERM l2 l4`
  (rw [] >>
  metis_tac [MAP_ZIP, PERM_MAP]);

Theorem list_type_v_to_list
  `!A l v.
    LIST_TYPE A l v ⇒
    ?l'. v_to_list v = SOME l' ∧ LIST_REL A l l'`
  (Induct_on `l` >>
  rw [LIST_TYPE_def, terminationTheory.v_to_list_def]
  >- EVAL_TAC >>
  rw [terminationTheory.v_to_list_def] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  rw [] >> EVAL_TAC);

Theorem string_list_uniq
  `!l1 l2.
    LIST_REL STRING_TYPE l1 l2 ⇒ l2 = MAP (λs. Litv (StrLit (explode s))) l1`
  (Induct_on `l1` >>
  rw [] >>
  `?s'. h = strlit s'` by metis_tac [mlstringTheory.mlstring_nchotomy] >>
  fs [STRING_TYPE_def]);

Theorem string_not_lt
  `¬(x < y) ⇔ (y:string) ≤ x`
  (rw[string_le_def]
  \\ metis_tac[string_lt_total,string_lt_antisym]);

Theorem strict_weak_order_string_cmp
  `strict_weak_order (λs1 s2. explode s1 < explode s2)`
  (rw [strict_weak_order_alt, transitive_def] >>
  metis_tac [string_lt_antisym, string_lt_trans, string_lt_total]);

Theorem string_le_transitive
  `transitive string_le`
  (rw[transitive_def,string_le_def]
  \\ metis_tac[string_lt_trans]);

Theorem string_le_antisymmetric
  `antisymmetric string_le`
  (rw[antisymmetric_def,string_le_def]
  \\ metis_tac[string_lt_antisym]);

Theorem SORTED_string_lt_le
  `SORTED string_lt ls ⇒ SORTED string_le ls`
  (strip_tac \\ match_mp_tac SORTED_weaken
  \\ asm_exists_tac \\ rw[string_le_def]);

Theorem validArg_filename
  `validArg x ∧ STRING_TYPE x v ⇒ FILENAME x v`
  (rw [validArg_def, FILENAME_def, EVERY_MEM, LENGTH_explode]);

Theorem validArg_filename_list
  `!x v. EVERY validArg x ∧ LIST_TYPE STRING_TYPE x v ⇒ LIST_TYPE FILENAME x v`
  (Induct_on `x` >>
  rw [LIST_TYPE_def, validArg_filename]);

val v_to_string_def = Define `
  v_to_string (Litv (StrLit s)) = s`;

Theorem LIST_REL_STRING_TYPE
  `LIST_REL STRING_TYPE ls vs ⇒ ls = MAP (implode o v_to_string) vs`
  (rw[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP] \\ rfs[] \\ res_tac \\
  Cases_on`EL x ls` \\ fs[STRING_TYPE_def,v_to_string_def,implode_def]);
(* -- *)

val usage_string_def = Define`
  usage_string = strlit"Usage: sort <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val get_file_contents = process_topdecs `
  (* Note: this is an accumulating version of TextIO.inputLines *)
  fun get_file_contents fd acc =
    case TextIO.inputLine fd of
      None => acc
    | Some l => get_file_contents fd (l::acc);

  fun get_files_contents files acc =
    case files of
      [] => acc
    | file::files =>
      let
        val fd = TextIO.openIn file
        val res = get_file_contents fd acc
      in
        (TextIO.closeIn fd;
         get_files_contents files res)
      end;`
val _ = append_prog get_file_contents;

(* TODO: these functions are generic, and should probably be moved *)
Theorem get_file_contents_spec
  `!fs fd fd_v acc_v acc.
    INSTREAM fd fd_v ∧
    IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_file_contents" (get_ml_prog_state()))
      [fd_v; acc_v]
      (STDIO fs)
      (POSTv strings_v.
        STDIO (fastForwardFD fs fd) *
        &(LIST_TYPE STRING_TYPE
            (MAP implode (REVERSE (linesFD fs fd) ++ acc))
            strings_v))`
  (ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fs fd)` >>
  rw [] >>
  xcf "get_file_contents" (get_ml_prog_state ()) >>
  `validFD fd fs` by metis_tac[get_file_content_validFD,IS_SOME_EXISTS,PAIR] \\
  xlet_auto >- xsimpl \\
  Cases_on `lineFD fs fd` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xvar >>
    xsimpl >>
    drule lineFD_NONE_lineForwardFD_fastForwardFD >>
    fs [GSYM linesFD_nil_lineFD_NONE] >>
    xsimpl)
  >- (
    xlet_auto
    >- (
      xret >>
      xsimpl) >>
    xapp >>
    xsimpl >>
    qexists_tac `emp` >>
    qexists_tac `lineForwardFD fs fd` >>
    qexists_tac `fd` >>
    qexists_tac `x::acc` >>
    xsimpl >>
    `?l1 lines. linesFD fs fd = l1::lines`
    by (
      Cases_on `linesFD fs fd` >>
      fs [linesFD_nil_lineFD_NONE]) >>
    drule linesFD_cons_imp >>
    rw [LIST_TYPE_def] >> xsimpl >>
    metis_tac [APPEND, APPEND_ASSOC]));

Theorem get_files_contents_spec
  `!fnames_v fnames acc_v acc fs.
    hasFreeFD fs ∧
    LIST_TYPE FILENAME fnames fnames_v ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_files_contents" (get_ml_prog_state ()))
      [fnames_v; acc_v]
      (STDIO fs)
      (POST
        (\strings_v.
          STDIO fs *
          &(LIST_TYPE STRING_TYPE
            (REVERSE (FLAT (MAP (all_lines fs o File) fnames))
              ++ (MAP implode acc))
             strings_v ∧
            EVERY (inFS_fname fs o File) fnames))
        (\e.
          STDIO fs *
          &(BadFileName_exn e ∧
          ¬EVERY (inFS_fname fs o File) fnames))
        (\n c b. &F))`
  (Induct_on `fnames` >>
  rw [] >>
  xcf "get_files_contents" (get_ml_prog_state ()) >>
  fs [LIST_TYPE_def] >>
  xmatch >>
  rw []
  >- (
    xvar >>
    xsimpl) >>
  qmatch_assum_rename_tac `FILENAME fname fname_v` >>
  reverse(Cases_on`STD_streams fs`)>-(fs[STDIO_def] \\ xpull) \\
  xlet_auto_spec(SOME (SPEC_ALL openIn_STDIO_spec))
  >- xsimpl
  >- xsimpl
  >- xsimpl >>
  qmatch_assum_abbrev_tac `validFD fd fs'` >>
  imp_res_tac nextFD_ltX \\
  imp_res_tac IS_SOME_get_file_content_openFileFS_nextFD \\ rfs[] \\
  pop_assum(qspecl_then[`0`,`ReadMode`]strip_assume_tac) \\ rfs[] \\
  xlet_auto >- (
    fs[Abbr`fs'`]
    \\ simp[get_mode_def, Abbr`fd`]
    \\ DEP_REWRITE_TAC[ALOOKUP_inFS_fname_openFileFS_nextFD]
    \\ simp[] ) \\
  imp_res_tac STD_streams_nextFD \\ rfs[] \\
  (* TODO: Update xlet_auto so that it can try different specs -
     xlet_auto works with close_STDIO_spec but not close_spec *)
  xlet_auto_spec(SOME (Q.SPECL[`fd`,`fastForwardFD fs' fd`] closeIn_STDIO_spec))
  >- (xsimpl \\ simp[Abbr`fs'`])
  >- (xsimpl  \\
    simp[Abbr`fs'`, validFileFD_def]
    \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ rfs[] )
  >- xsimpl >>
  xapp >>
  xsimpl >>
  simp[Abbr`fs'`,Abbr`fd`,openFileFS_A_DELKEY_nextFD] >>
  full_simp_tac std_ss [GSYM MAP_APPEND] >>
  instantiate >> xsimpl >>
  simp[REVERSE_APPEND,MAP_REVERSE,linesFD_openFileFS_nextFD,MAP_MAP_o,o_DEF]);
(* -- *)

val _ = (append_prog o process_topdecs) `
  fun sort () =
    let val contents_list =
      case CommandLine.arguments () of
        [] => get_file_contents TextIO.stdIn []
      | files => get_files_contents files []
    val contents_array = Array.fromList contents_list
    in
      (quicksort String.< contents_array;
       Array.app TextIO.print contents_array)
    end
    handle TextIO.BadFileName => TextIO.output TextIO.stdErr "Cannot open file"`;

val valid_sort_result_def = Define`
  valid_sort_result cl init_fs result_fs ⇔
    let inodes = if LENGTH cl > 1
                 then MAP File (TL cl)
                 else [IOStream(strlit"stdin")] in
    if LENGTH cl ≤ 1 ∨ EVERY (inFS_fname init_fs) inodes then
      let lines = FLAT (MAP (all_lines init_fs) inodes) in
      let fs = if LENGTH cl ≤ 1 then fastForwardFD init_fs 0 else init_fs in
      ∃output.
        PERM output lines ∧
        SORTED mlstring_le output ∧
        result_fs = add_stdout fs (concat output)
    else result_fs = add_stderr init_fs (strlit "Cannot open file")`;

Theorem valid_sort_result_unique
  `valid_sort_result cl fs fs1 ∧
   valid_sort_result cl fs fs2 ⇒
   fs1 = fs2`
  (rw[valid_sort_result_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ match_mp_tac (MP_CANON SORTED_PERM_EQ)
  \\ instantiate
  \\ simp[transitive_mlstring_le,antisymmetric_mlstring_le]
  \\ metis_tac[PERM_SYM,PERM_TRANS]);

Theorem valid_sort_result_exists
  `∃r. valid_sort_result cl fs r`
  (rw[valid_sort_result_def]
  \\ TRY CASE_TAC
  \\ PROVE_TAC[QSORT_SORTED, QSORT_PERM, PERM_SYM, total_def,
               total_mlstring_le, transitive_mlstring_le ]);

Theorem valid_sort_result_numchars
  `valid_sort_result cl fs1 fs2 ⇒ fs2.numchars = fs1.numchars`
  (rw[valid_sort_result_def] \\ rw[]);

val sort_sem_def = new_specification("sort_sem_def",["sort_sem"],
  valid_sort_result_exists
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM]);

Theorem sort_sem_intro
  `(∀out. valid_sort_result cl fs out ⇒ P out)
   ⇒ P (sort_sem cl fs)`
  (metis_tac[sort_sem_def,valid_sort_result_unique]);

Theorem sort_sem_numchars[simp]
  `(sort_sem cl fs).numchars = fs.numchars`
  (DEEP_INTRO_TAC sort_sem_intro
  \\ metis_tac[valid_sort_result_numchars]);

val SORTED_mlstring_le = prove(
  ``!output. SORTED mlstring_le output = SORTED $<= (MAP explode output)``,
  Induct \\ fs [SORTED_DEF]
  \\ Cases_on `output` \\ fs [SORTED_DEF]
  \\ Cases \\ Cases_on `h`
  \\ fs [explode_def,strlit_le_strlit]);

Theorem sort_spec
  `(if LENGTH cl ≤ 1 then (∃input. get_file_content fs 0 = SOME (input,0)) else hasFreeFD fs)
    ⇒
    app (p : 'ffi ffi_proj) ^(fetch_v "sort" (get_ml_prog_state ()))
      [Conv NONE []]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
        &UNIT_TYPE () uv *
          STDIO (sort_sem cl fs) * COMMANDLINE cl)`
  (xcf "sort" (get_ml_prog_state ()) >>
  xmatch >>
  qabbrev_tac `fnames = TL cl` >>
  qabbrev_tac `inodes = if LENGTH cl > 1 then MAP File fnames else [IOStream(strlit"stdin")]` >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) >>
  fs[wfcl_def] >>
  reverse(Cases_on`MEM (IOStream(strlit"stdin")) (MAP FST fs.files)`)
  >- (
    fs[STDIO_def,IOFS_def,wfFS_def] \\ xpull
    \\ fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD]
    \\ `F` suffices_by simp[]
    \\ fs[STD_streams_def]
    \\ last_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
    \\ rewrite_tac[] \\ strip_tac
    \\ imp_res_tac ALOOKUP_MEM \\ res_tac \\ fs[]
    \\ rw[] \\ fs[]
    \\ metis_tac[] ) \\
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull) >>
  reverse (xhandle
    `POST
      (\uv. &(UNIT_TYPE () uv ∧
              EVERY (inFS_fname fs) inodes) *
            STDIO (sort_sem cl fs) * COMMANDLINE cl)
      (\e.  &(BadFileName_exn e ∧
              ¬EVERY (inFS_fname fs) inodes) *
            STDIO fs * COMMANDLINE cl)
      (\n c b. &F)`) >>
  xsimpl
  >- (
    fs [BadFileName_exn_def] >>
    xcases >>
    xapp_spec output_stderr_spec >>
    xsimpl >>
    DEEP_INTRO_TAC sort_sem_intro >>
    simp[valid_sort_result_def] \\
    Cases_on`LENGTH cl > 1` \\ fs[]
    >- (
      TOP_CASE_TAC \\ fs[EVERY_MEM,EXISTS_MEM]
      >- metis_tac[] \\
      CONV_TAC SWAP_EXISTS_CONV \\
      qexists_tac`fs` \\
      xsimpl ) \\
    fs[Abbr`inodes`] \\
    fs[inFS_fname_def,MEM_MAP,EXISTS_PROD] ) >>
  xlet_auto
  >- (xret >> xsimpl) >>
  xlet_auto >- xsimpl >>
  xlet
    `POST
       (\strings_v.
          COMMANDLINE cl * STDIO (if LENGTH cl ≤ 1 then fastForwardFD fs 0 else fs) *
          &(LIST_TYPE STRING_TYPE
             (REVERSE (FLAT (MAP (all_lines fs) inodes))) strings_v ∧
            EVERY (inFS_fname fs) inodes))
       (\e.
          COMMANDLINE cl * STDIO fs *
          &(BadFileName_exn e ∧
          ¬EVERY (inFS_fname fs) inodes))
       (\n c b. &F)` >>
  xsimpl
  >- (
    `?command args. cl = command::args`
    by (
      Cases_on `cl` >>
      fs [] >>
      metis_tac []) >>
    fs [LIST_TYPE_def, Abbr `fnames`] >>
    Cases_on`args` >- (
      fs[LIST_TYPE_def] \\ rveq \\ fs[] \\
      xmatch \\
      xlet_auto >- (xcon \\ xsimpl) \\
      xapp \\
      simp[IS_SOME_EXISTS,PULL_EXISTS,EXISTS_PROD] \\
      instantiate \\
      CONV_TAC(RESORT_EXISTS_CONV List.rev) \\ qexists_tac`[]` \\
      simp[LIST_TYPE_def,Abbr`inodes`] \\
      xsimpl \\
      simp[linesFD_def,inFS_fname_def,INSTREAM_def,
           FD_def,stdin_v_thm,GSYM stdIn_def] \\
      rw[STD_streams_get_mode] \\
      fs[get_file_content_def,all_lines_def,lines_of_def] \\
      pairarg_tac \\ fs[] \\
      `fnm = IOStream(strlit"stdin")` by metis_tac[STD_streams_def,PAIR_EQ,SOME_11] \\
      fs[mlstringTheory.strcat_thm,MAP_MAP_o,MAP_REVERSE,o_DEF])
    \\ fs[LIST_TYPE_def]
    \\ xmatch
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ xapp
    \\ simp[LIST_TYPE_def]
    \\ qpat_assum`_ = _::_`(mp_tac o Q.AP_TERM`LENGTH`)
    \\ simp_tac(srw_ss())[] \\ strip_tac \\ fs[]
    \\ instantiate \\ xsimpl
    \\ qmatch_asmsub_abbrev_tac`command::args`
    \\ qexists_tac`args`
    \\ qexists_tac`[]` \\ fs[LIST_TYPE_def]
    \\ conj_tac
    >- (
      fs[Abbr`args`,LIST_TYPE_def] \\
      fs[quantHeuristicsTheory.LIST_LENGTH_COMPARE_SUC] \\
      rveq \\ fs[] \\ rveq \\
      fs[FILENAME_def,validArg_def,EVERY_MEM] \\
      match_mp_tac LIST_TYPE_mono \\
      asm_exists_tac \\
      fs[FILENAME_def,MEM_MAP,PULL_EXISTS] )
    \\ `inodes = MAP File args` by simp[Abbr`inodes`,Abbr`args`]
    \\ qunabbrev_tac`inodes` \\ pop_assum SUBST_ALL_TAC
    \\ simp[MAP_MAP_o,EVERY_MAP,o_DEF,EXISTS_MAP] ) >>
  qmatch_assum_abbrev_tac `LIST_TYPE STRING_TYPE strings strings_v` >>
  imp_res_tac list_type_v_to_list \\
  xlet_auto >- xsimpl \\
  assume_tac strict_weak_order_string_cmp \\
  xlet_auto >- (
    xsimpl
    \\ mp_tac StringProgTheory.mlstring_lt_v_thm
    \\ simp[mlstringTheory.mlstring_lt_inv_image,inv_image_def] )
  \\ xapp >>
  xsimpl >>
  qexists_tac `COMMANDLINE cl` >>
  xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fs0` >>
  qexists_tac `\l n. STDIO (add_stdout fs0 (implode (CONCAT (MAP v_to_string (TAKE n l)))))` >>
  xsimpl >>
  simp [implode_def] >>
  DEP_REWRITE_TAC[GEN_ALL add_stdo_nil] >>
  conj_asm1_tac
  >- (
    simp[Abbr`fs0`]
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
    `s1 = s2` suffices_by xsimpl \\
    simp[Abbr`s1`,Abbr`s2`] \\
    simp [concat_def] \\
    AP_TERM_TAC \\
    drule PERM_ZIP \\
    imp_res_tac LIST_REL_LENGTH \\
    disch_then(last_assum o mp_then (Pos (el 3)) mp_tac) \\ simp[] \\
    disch_then(first_assum o mp_then (Pos (el 2)) mp_tac) \\ simp[] \\
    qmatch_assum_abbrev_tac`PERM output orig` \\
    `orig = REVERSE strings`
      by simp[Abbr`orig`,Abbr`strings`,MAP_REVERSE] \\
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
    fs []));

Theorem sort_whole_prog_spec
  `(if LENGTH cl ≤ 1 then (∃input. get_file_content fs 0 = SOME (input,0)) else hasFreeFD fs)
   ⇒ whole_prog_spec ^(fetch_v "sort" (get_ml_prog_state())) cl fs NONE (valid_sort_result cl fs)`
  (disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qexists_tac`sort_sem cl fs`
  \\ reverse conj_tac
  >- metis_tac[with_same_numchars,sort_sem_numchars,sort_sem_def]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH sort_spec)))
  \\ xsimpl);

val (sem_thm,prog_tm) = whole_prog_thm (get_ml_prog_state ()) "sort" (UNDISCH sort_whole_prog_spec)
val sort_prog_def = Define `sort_prog = ^prog_tm`;

val sort_semantics =
  sem_thm |> ONCE_REWRITE_RULE[GSYM sort_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "sort_semantics";

val _ = export_theory ();
