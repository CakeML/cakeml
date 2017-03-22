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
        (FileIO.closeIn fd;
         res)
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

