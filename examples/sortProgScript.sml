open preamble basis quicksortProgTheory

val _ = new_theory "sortProg";

val _ = translation_extends"quicksortProg";

(* TODO: move *)
val perm_zip = Q.store_thm ("perm_zip",
  `!l1 l2 l3 l4.
    LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1,l2)) (ZIP (l3,l4))
    ⇒
    PERM l1 l3 ∧ PERM l2 l4`,
  rw [] >>
  metis_tac [MAP_ZIP, PERM_MAP]);

val list_type_v_to_list = Q.store_thm ("list_type_v_to_list",
  `!A l v.
    LIST_TYPE A l v ⇒
    ?l'. v_to_list v = SOME l' ∧ LIST_REL A l l'`,
  Induct_on `l` >>
  rw [LIST_TYPE_def, terminationTheory.v_to_list_def] >>
  rw [terminationTheory.v_to_list_def] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  rw []);

val string_list_uniq = Q.store_thm ("string_list_uniq",
  `!l1 l2.
    LIST_REL STRING_TYPE l1 l2 ⇒ l2 = MAP (λs. Litv (StrLit (explode s))) l1`,
  Induct_on `l1` >>
  rw [] >>
  `?s'. h = strlit s'` by metis_tac [mlstringTheory.mlstring_nchotomy] >>
  fs [STRING_TYPE_def]);

val char_lt_total = Q.store_thm ("char_lt_total",
  `!(c1:char) c2. ¬(c1 < c2) ∧ ¬(c2 < c1) ⇒ c1 = c2`,
  rw [char_lt_def, CHAR_EQ_THM]);

val string_lt_total = Q.store_thm ("string_lt_total",
  `!(s1:string) s2. ¬(s1 < s2) ∧ ¬(s2 < s1) ⇒ s1 = s2`,
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def, char_lt_total]
  >- (
    Cases_on `s1` >>
    fs [string_lt_def]) >>
  metis_tac [char_lt_total]);

val string_not_lt = Q.store_thm("string_not_lt",
  `¬(x < y) ⇔ (y:string) ≤ x`,
  rw[string_le_def]
  \\ metis_tac[string_lt_total,string_lt_antisym]);

val strict_weak_order_string_cmp = Q.store_thm ("strict_weak_order_string_cmp",
  `strict_weak_order (λs1 s2. explode s1 < explode s2)`,
  rw [strict_weak_order_alt, transitive_def] >>
  metis_tac [string_lt_antisym, string_lt_trans, string_lt_total]);

val string_le_transitive = Q.store_thm("string_le_transitive",
  `transitive string_le`,
  rw[transitive_def,string_le_def]
  \\ metis_tac[string_lt_trans]);

val string_le_antisymmetric = Q.store_thm("string_le_antisymmetric",
  `antisymmetric string_le`,
  rw[antisymmetric_def,string_le_def]
  \\ metis_tac[string_lt_antisym]);

val SORTED_string_lt_le = Q.store_thm("SORTED_string_lt_le",
  `SORTED string_lt ls ⇒ SORTED string_le ls`,
  strip_tac \\ match_mp_tac SORTED_weaken
  \\ asm_exists_tac \\ rw[string_le_def]);

val validArg_filename = Q.store_thm ("validArg_filename",
  `validArg (explode x) ∧ STRING_TYPE x v ⇒ FILENAME x v`,
  rw [validArg_def, FILENAME_def, EVERY_MEM, LENGTH_explode]);

val validArg_filename_list = Q.store_thm ("validArg_filename_list",
  `!x v. EVERY validArg (MAP explode x) ∧ LIST_TYPE STRING_TYPE x v ⇒ LIST_TYPE FILENAME x v`,
  Induct_on `x` >>
  rw [LIST_TYPE_def, validArg_filename]);

val v_to_string_def = Define `
  v_to_string (Litv (StrLit s)) = s`;

val LIST_REL_STRING_TYPE = Q.store_thm("LIST_REL_STRING_TYPE",
  `LIST_REL STRING_TYPE ls vs ⇒ ls = MAP (implode o v_to_string) vs`,
  rw[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP] \\ rfs[] \\ res_tac \\
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
      NONE => acc
    | SOME l => get_file_contents fd (l::acc);

  fun get_files_contents files acc =
    case files of
      [] => acc
    | file::files =>
      let
        val fd = TextIO.openIn file
        val res = get_file_contents fd acc
      in
        (TextIO.close fd;
         get_files_contents files res)
      end;`
val _ = append_prog get_file_contents;

(* TODO: these functions are generic, and should probably be moved *)
val get_file_contents_spec = Q.store_thm ("get_file_contents_spec",
  `!fs fd fd_v acc_v acc.
    WORD (n2w fd : word8) fd_v ∧
    IS_SOME (get_file_content fs fd) ∧
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
            strings_v))`,
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fs fd)` >>
  rw [] >>
  xcf "get_file_contents" (get_ml_prog_state ()) >>
  `validFD fd fs` by metis_tac[get_file_content_validFD,IS_SOME_EXISTS,PAIR] \\
  reverse(Cases_on`fd ≤ 255`) >- (fs[STDIO_def,IOFS_def,wfFS_def,validFD_def] \\ xpull \\ metis_tac[]) \\
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

val get_files_contents_spec = Q.store_thm ("get_files_contents_spec",
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
            ¬EVERY (inFS_fname fs o File) fnames)))`,
  Induct_on `fnames` >>
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
  >- xsimpl >>
  qmatch_assum_abbrev_tac `validFD fd fs'` >>
  imp_res_tac nextFD_leX \\
  imp_res_tac IS_SOME_get_file_content_openFileFS_nextFD \\
  pop_assum(qspec_then`0`strip_assume_tac) \\ rfs[] \\
  (* TODO: xlet_auto should be figuring this out *)
  xlet_auto_spec(SOME(SPEC_ALL(Q.SPEC`fs'` get_file_contents_spec))) \\
  imp_res_tac STD_streams_nextFD \\ rfs[] \\
  (* TODO: xlet_auto should be figuring this out *)
  xlet_auto_spec(SOME (Q.SPECL[`fd`,`fastForwardFD fs' fd`] close_STDIO_spec))
  >- xsimpl
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
      case Commandline.arguments () of
        [] => get_file_contents TextIO.stdIn []
      | files => get_files_contents files []
    val contents_array = Array.fromList contents_list
    in
      (quicksort String.< contents_array;
       Array.app TextIO.print_string contents_array)
    end
    handle TextIO.BadFileName => TextIO.prerr_string "Cannot open file"`;

val valid_sort_result_def = Define`
  valid_sort_result cl init_fs result_fs ⇔
    let inodes = if LENGTH cl > 1
                 then MAP File (TL (MAP implode cl))
                 else [IOStream(strlit"stdin")] in
    if LENGTH cl ≤ 1 ∨ EVERY (inFS_fname init_fs) inodes then
      let lines = MAP explode (FLAT (MAP (all_lines init_fs) inodes)) in
      let fs = if LENGTH cl ≤ 1 then fastForwardFD init_fs 0 else init_fs in
      ∃output.
        PERM output lines ∧
        SORTED $<= output ∧
        result_fs = add_stdout fs (FLAT output)
    else result_fs = add_stderr init_fs "Cannot open file"`;

val valid_sort_result_unique = Q.store_thm("valid_sort_result_unique",
  `valid_sort_result cl fs fs1 ∧
   valid_sort_result cl fs fs2 ⇒
   fs1 = fs2`,
  rw[valid_sort_result_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ match_mp_tac (MP_CANON SORTED_PERM_EQ)
  \\ instantiate
  \\ simp[string_le_transitive,string_le_antisymmetric]
  \\ metis_tac[PERM_SYM,PERM_TRANS]);

val valid_sort_result_exists = Q.store_thm("valid_sort_result_exists",
  `∃r. valid_sort_result cl fs r`,
  rw[valid_sort_result_def]
  \\ TRY CASE_TAC
  \\ PROVE_TAC[QSORT_SORTED, QSORT_PERM, PERM_SYM, total_def,
               string_le_def, string_lt_total, string_le_transitive ]);

val sort_sem_def = new_specification("sort_sem_def",["sort_sem"],
  valid_sort_result_exists
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM]);

val sort_sem_intro = Q.store_thm("sort_sem_intro",
  `(∀out. valid_sort_result cl fs out ⇒ P out)
   ⇒ P (sort_sem cl fs)`,
  metis_tac[sort_sem_def,valid_sort_result_unique]);

val STD_streams_sort_sem = Q.store_thm("STD_streams_sort_sem",
  `STD_streams fs ⇒ STD_streams (sort_sem cl fs)`,
  DEEP_INTRO_TAC sort_sem_intro \\
  rw[valid_sort_result_def] \\
  simp[STD_streams_fastForwardFD,STD_streams_add_stdout,STD_streams_add_stderr]);

val sort_spec = Q.store_thm ("sort_spec",
  `!cl fs out err.
    (if LENGTH cl ≤ 1 then (∃input. get_file_content fs 0 = SOME (input,0)) else hasFreeFD fs)
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "sort" (get_ml_prog_state ()))
      [Conv NONE []]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
        &UNIT_TYPE () uv *
          STDIO (sort_sem cl fs) * COMMANDLINE cl)`,
  xcf "sort" (get_ml_prog_state ()) >>
  xmatch >>
  qabbrev_tac `fnames = TL (MAP implode cl)` >>
  qabbrev_tac `inodes = if LENGTH cl > 1 then MAP File fnames else [IOStream(strlit"stdin")]` >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) >>
  fs[wfcl_def] >>
  reverse(Cases_on`MEM (IOStream(strlit"stdin")) (MAP FST fs.files)`)
  >- (
    fs[STDIO_def,IOFS_def,wfFS_def] \\ xpull
    \\ fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD]
    \\ `F` suffices_by simp[]
    \\ fs[STD_streams_def]
    \\ last_assum(qspecl_then[`0`,`inp`]mp_tac)
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
            STDIO fs * COMMANDLINE cl)`) >>
  xsimpl
  >- (
    fs [BadFileName_exn_def] >>
    xcases >>
    xapp >>
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
    fs[inFS_fname_def,MEM_MAP,EXISTS_PROD] )
  >- (
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
              ¬EVERY (inFS_fname fs) inodes))` >>
    xsimpl
    >- (
      `?command args. MAP implode cl = command::args`
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
        simp[linesFD_def,inFS_fname_def] \\
        conj_tac >- metis_tac[stdIn_def,stdin_v_thm] \\
        fs[get_file_content_def,all_lines_def] \\
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
    qexists_tac `\l n. STDIO (add_stdout fs0 (CONCAT (MAP v_to_string (TAKE n l))))` >>
    xsimpl >>
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
      xsimpl)
    >- (
      DEEP_INTRO_TAC sort_sem_intro \\
      rw[valid_sort_result_def] \\
      qmatch_abbrev_tac`STDIO (add_stdout _ s1) * _ ==>> STDIO (add_stdout _ s2) *_` \\
      `s1 = s2` suffices_by xsimpl \\
      simp[Abbr`s1`,Abbr`s2`] \\
      AP_TERM_TAC \\
      drule PERM_ZIP \\
      imp_res_tac LIST_REL_LENGTH \\
      disch_then(last_assum o mp_then (Pos (el 3)) mp_tac) \\ simp[] \\
      disch_then(first_assum o mp_then (Pos (el 2)) mp_tac) \\ simp[] \\
      qmatch_assum_abbrev_tac`PERM output orig` \\
      `orig = REVERSE (MAP explode strings)`
        by simp[Abbr`orig`,Abbr`strings`,MAP_REVERSE] \\
      fs[Abbr`orig`] \\ strip_tac \\
      match_mp_tac (MP_CANON SORTED_PERM_EQ) \\
      goal_assum(first_assum o mp_then Any mp_tac) \\
      simp[string_le_transitive,string_le_antisymmetric] \\
      fs[GSYM inv_image_def,string_not_lt] \\
      fs[GSYM sorted_map,string_le_transitive] \\
      imp_res_tac LIST_REL_STRING_TYPE \\ rveq \\
      fs[MAP_MAP_o,o_DEF,ETA_AX] \\
      metis_tac[PERM_MAP,PERM_TRANS,PERM_SYM]
    )));

val spec = sort_spec |> SPEC_ALL |> UNDISCH_ALL |> SIMP_RULE(srw_ss())[STDIO_def] |> add_basis_proj;
val name = "sort"
val (sem_thm,prog_tm) = call_thm (get_ml_prog_state ()) name spec
val sort_prog_def = Define `sort_prog = ^prog_tm`;

val length_gt_1_not_null =
  Q.prove(`LENGTH cls > 1 ⇒ ¬ NULL cls`, rw[NULL_EQ] \\ strip_tac \\ fs[]);

val sort_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM sort_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[PULL_EXISTS,AND_IMP_INTRO,GSYM CONJ_ASSOC,STD_streams_sort_sem]
  |> curry save_thm "sort_semantics";

val _ = export_theory ();
