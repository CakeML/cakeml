open preamble ml_translatorLib ml_progLib;
open cfTacticsLib basisFunctionsLib;
open rofsFFITheory mlfileioProgTheory ioProgTheory;
open quicksortProgTheory;

val _ = new_theory "sortProg";

val _ = translation_extends"ioProg";

fun basis_st () = get_ml_prog_state ();

val usage_string_def = Define`
  usage_string = strlit"Usage: sort <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val get_file_contents = process_topdecs `
  fun get_file_contents fd acc =
    case FileIO.inputLine fd of
      NONE => acc
    | SOME l => get_file_contents fd (l::acc)`;

val gfc_st = ml_progLib.add_prog get_file_contents pick_name (basis_st ());

val get_files_contents = process_topdecs `
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
      end`;

val gfsc_st = ml_progLib.add_prog get_files_contents pick_name gfc_st;

val sort = process_topdecs `
  fun sort u =
    let val contents_list =
      case Commandline.arguments () of
        [] => get_file_contents FileIO.stdIn []
      | files => get_files_contents files []
    val contents_array = Array.fromList contents_list
    val sorted = quicksort String.compare contents_array
    in
      List.app print sorted
    end`;

val sort_st = ml_progLib.add_prog sort pick_name gfsc_st;

val _ = export_theory ();

