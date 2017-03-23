open preamble ml_translatorTheory ml_translatorLib ml_progLib;
open cfTacticsLib basisFunctionsLib;
open rofsFFITheory mlfileioProgTheory ioProgTheory;
open quicksortProgTheory;

val _ = new_theory "sortProg";

val _ = translation_extends"ioProg";

val usage_string_def = Define`
  usage_string = strlit"Usage: sort <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val get_file_contents = process_topdecs `
  fun get_file_contents fd acc =
    case FileIO.inputLine fd of
      NONE => acc
    | SOME l => get_file_contents fd (l::acc);

  fun get_files_contents files acc =
    case files of
      [] => acc
    | file::files =>
      let
        val fd = FileIO.openIn file
        val res = get_file_contents fd acc
      in
        (FileIO.close fd;
         get_files_contents files res)
      end;

  fun sort () =
    let val contents_list =
      case Commandline.arguments () of
        [] => get_file_contents FileIO.stdIn []
      | files => get_files_contents files []
    val contents_array = Array.fromList contents_list
    val sorted = quicksort String.compare contents_array
    in
      List.app print sorted
    end`;

val _ = append_prog get_file_contents;

val wfFS_bumpLineFD = Q.store_thm ("wfFS_bumpLineFD",
  `!fs fd.
    wfFS fs
    ⇒
    wfFS (bumpLineFD fd fs)`,
  rw [bumpLineFD_def] >>
  every_case_tac >>
  fs [wfFS_def] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw [ALIST_FUPDKEY_ALOOKUP]);

val get_file_contents_spec = Q.store_thm ("get_file_contents_spec",
  `!fs fd fd_v acc_v acc.
    WORD (n2w fd : word8) fd_v ∧
    wfFS fs ∧
    validFD fd fs ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_file_contents" (get_ml_prog_state()))
      [fd_v; acc_v]
      (ROFS fs)
      (POSTv strings_v.
        ROFS (bumpAllFD fd fs) *
        &(LIST_TYPE STRING_TYPE
            (MAP implode (REVERSE (MAP (\l. l++"\n") (linesFD fd fs)) ++ acc))
            strings_v))`,
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fd fs)` >>
  rw [] >>
  xcf "get_file_contents" (get_ml_prog_state ()) >>
  xlet
    `POSTv line_v.
      ROFS (bumpLineFD fd fs) *
      &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline fd fs)) line_v`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `GC` >>
    qexists_tac `fs` >>
    qexists_tac `n2w fd` >>
    simp [] >>
    xsimpl >>
    fs [wfFS_def, validFD_def] >>
    first_x_assum drule >>
    rw [] >>
    xsimpl) >>
  Cases_on `FDline fd fs` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xvar >>
    xsimpl >>
    drule FDline_NONE_bumpAll_bumpLine >>
    fs [FDline_NONE_linesFD] >>
    xsimpl)
  >- (
    xlet
      `POSTv new_acc_v.
        ROFS (bumpLineFD fd fs) *
        &LIST_TYPE STRING_TYPE (MAP implode (x::acc)) new_acc_v`
    >- (
      xret >>
      xsimpl >>
      simp [LIST_TYPE_def]) >>
    xapp >>
    xsimpl >>
    qexists_tac `GC` >>
    qexists_tac `bumpLineFD fd fs` >>
    qexists_tac `fd` >>
    qexists_tac `x::acc` >>
    xsimpl >>
    `?l1 lines. linesFD fd fs = l1::lines`
    by (
      Cases_on `linesFD fd fs` >>
      fs [GSYM FDline_NONE_linesFD]) >>
    drule linesFD_eq_cons_imp >>
    rw []
    >- metis_tac [wfFS_bumpLineFD]
    >- metis_tac [APPEND, APPEND_ASSOC]));

val get_files_contents_spec = Q.store_thm ("get_files_contents_spec",
  `!fnames_v fnames acc_v acc fs.
    wfFS fs ∧
    CARD (FDOM (alist_to_fmap fs.infds)) < 255 ∧
    LIST_TYPE FILENAME fnames fnames_v ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_files_contents" (get_ml_prog_state ()))
      [fnames_v; acc_v]
      (ROFS fs)
      (POST
        (\strings_v.
          ROFS fs *
          &(LIST_TYPE STRING_TYPE
             (MAP (\str. implode (str ++ "\n"))
               (REVERSE
                 (FLAT
                   (MAP (\fname. splitlines (THE (ALOOKUP fs.files fname))) fnames)))
              ++ (MAP implode acc))
             strings_v ∧
            EVERY (\fname. inFS_fname fs fname) fnames))
        (\e.
          ROFS fs *
          &(BadFileName_exn e ∧
            EXISTS (\fname. ~inFS_fname fs fname) fnames)))`,
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
  xlet
    `(POST
       (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
               validFD (nextFD fs) (openFileFS fname fs) ∧
               inFS_fname fs fname) *
             ROFS (openFileFS fname fs))
       (\e. &(BadFileName_exn e ∧ ~inFS_fname fs fname) * ROFS fs))`
  >- (
    xapp >>
    xsimpl)
  >- xsimpl >>
  qmatch_assum_abbrev_tac `validFD fd fs'` >>
  xlet
    `POSTv strings_v.
       ROFS (bumpAllFD fd fs') *
       &(LIST_TYPE STRING_TYPE
          (MAP implode (REVERSE (MAP (\l. l++"\n") (linesFD fd fs')) ++ acc))
          strings_v)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `GC` >>
    qexists_tac `fs'` >>
    qexists_tac `fd` >>
    qexists_tac `acc` >>
    xsimpl >>
    metis_tac [wfFS_openFile]) >>
  xlet `POSTv u. ROFS (bumpAllFD fd fs' with infds updated_by A_DELKEY fd)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `GC` >>
    qexists_tac `bumpAllFD fd fs'` >>
    qexists_tac `n2w fd` >>
    xsimpl >>
    `fd < 255` by metis_tac [nextFD_ltX] >>
    rw [] >>
    xsimpl) >>
  xapp >>
  xsimpl >>
  qexists_tac `GC` >>
  qexists_tac `fs` >>
  qexists_tac `REVERSE (MAP (λl. STRCAT l "\n") (linesFD fd fs')) ++ acc` >>
  rw [] >>
  `bumpAllFD fd fs' with infds updated_by A_DELKEY fd = fs`
  by (
    rw [RO_fs_component_equality, Abbr`fs'`, Abbr `fd`] >>
    irule A_DELKEY_nextFD_openFileFS >>
    rw [nextFD_ltX]) >>
  xsimpl >>
  fs [REVERSE_APPEND, MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF] >>
  `splitlines (THE (ALOOKUP fs.files fname)) = linesFD fd fs'`
  by (
    simp [linesFD_def, Abbr `fd`, Abbr `fs'`] >>
    drule ALOOKUP_inFS_fname_openFileFS_nextFD >>
    simp [nextFD_ltX] >>
    drule inFS_fname_ALOOKUP_EXISTS >>
    rw [] >>
    rw [] >>
    Cases_on `0 < STRLEN content` >>
    simp [libTheory.the_def, GSYM LENGTH_NIL]) >>
  simp []);



val spec = sort_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "sort"
val (sem_thm,prog_tm) = ioProgLib.call_thm sort_st name spec
val sort_prog_def = Define `sort = ^prog_tm`;
val sort_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE[GSYM sort_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[wfFS_def,inFS_fname_def]
  |> curry save_thm "sort_semantics_thm";


val _ = export_theory ();
