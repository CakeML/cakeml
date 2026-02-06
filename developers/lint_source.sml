(*
   This SML program performs source linting on CakeML source files.
   It checks for:
    - trailing whitespace
    - tab characters
    - lines exceeding the maximum length
    - banned HOL4 constructs (e.g. store_thm, Hol_datatype)

   Usage:
    lint_source file1 file2 ...   lint specific files
    lint_source --all [path]      recursively lint all source files under path
*)

(* Constants *)

val MAX_CODE_LINE_LENGTH = 200

val AUTO_INCLUDE_SUFFIXES = ["Script.sml","Syntax.sml","Lib.sml",".lem",".c",".cml"]

val ILLEGAL_STRINGS =
  [("store_thm(\"", "The Theorem syntax is to be used instead of store_thm."),
   ("type_abbrev(\"", "The Type syntax is to be used instead of type_abbrev."),
   ("overload_on(\"", "Use Overload ... = ``...`` instead of overload_on."),
   (* Bans constructs such as `map overload_on ...` where ... is a list literal *)
   ("overload_on"^"[", "Use Overload ... = ``...`` instead of overload_on."),
   ("Hol_datatype"^"`", "Use Datatype: ... End syntax instead of Hol_datatype."),
   ("Datatype"^"`", "Use Datatype: ... End syntax instead of Datatype with `"),
   (* \226\128\152 corresponds to ' *)
   ("Datatype"^"\226\128\152", "Use Datatype: ... End syntax instead of Datatype\226\128\152."),
   ("Hol_rel"^"n`","Use Inductive ... End instead of old Hol_reln."),
   ("Hol_rel"^"n\"","Use Inductive ... End instead of old Hol_reln."),
   ("Hol_corel"^"n`","Use CoInductive ... End instead of old Hol_coreln."),
   (* HACK Stop lint_source from flagging itself by using \ \ in strings *)
   ("new_\ \theory","Use Theory syntax instead of old new_\ \theory"),
   ("export_\ \theory","Use Theory sytnax instead of old export_\ \theory"),
   ("TheoryPP.include_\ \docs","Add the no_sig_docs tag to the theory name instead of TheoryPP.include_\ \docs."),
   ("Trivialit\ \y", "Trivialit\ \y has been deprecated. Please use Theorem with a local tag instead.")
  ]

(* Helper functions *)

exception LintExn of string;

fun fail str = raise LintExn str;

fun err s = (print s; print "\n"; OS.Process.exit OS.Process.failure; false);

fun mem x [] = false
  | mem x (y::ys) = if x = y then true else mem x ys;

(* Reading a file *)

fun read_all_lines filename =
  let
    val f = TextIO.openIn(filename)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line => line :: read_rest ()
    val all_lines = read_rest ()
    val _ = TextIO.closeIn f
  in SOME all_lines end
  handle e => NONE;

fun every_line_in_file filename p =
  let
    val f = TextIO.openIn(filename)
    fun every_line n =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line => (p n line; every_line (n+1))
    val _ = every_line 1
    val _ = TextIO.closeIn f
  in () end;

(* Linting checks *)

fun assert_no_trailing_whitespace n line =
  if String.isSuffix " \n" line orelse String.isSuffix " " line
  then fail "trailing white-space is not allowed (adjust your editor setting)"
  else ()

fun assert_no_tabs_in_line n line =
  if String.isSubstring "\t" line
  then fail "tab characters (#\"\\t\") are not allowed"
  else ()

fun assert_line_length_OK n line =
  if MAX_CODE_LINE_LENGTH < size line
  then fail ("line " ^ Int.toString n ^ " is longer than " ^
             Int.toString MAX_CODE_LINE_LENGTH)
  else ()

fun check_for_illegal_strings filename NONE = ()
  | check_for_illegal_strings filename (SOME all_lines) =
  if String.isSuffix "Lib.sml" filename then () else let
  val spaces = explode " \n\t"
  fun remove_spaces c = if mem c spaces then "" else implode [c]
  val entire_file_as_str = String.translate remove_spaces (concat all_lines)
  fun check_each (ill_str, err_msg) =
    if String.isSubstring ill_str entire_file_as_str
    then fail err_msg else ()
  in List.app check_each ILLEGAL_STRINGS end

fun lint_file filename = let
  val _ = every_line_in_file filename
            (fn n => fn line => ( assert_no_trailing_whitespace n line ;
                                  assert_no_tabs_in_line n line ;
                                  assert_line_length_OK n line ))
  val _ = check_for_illegal_strings filename (read_all_lines filename)
  in () end

(* Directory traversal *)

fun is_dir filename =
  OS.FileSys.isDir filename handle OS.SysErr _ => false;

fun all_filenames_from_path path = let
  val d = OS.FileSys.openDir(path)
  fun all () =
    case OS.FileSys.readDir(d) of
      NONE => [] | SOME name => name :: all ()
  val names = all ()
  val _ = OS.FileSys.closeDir(d)
  in names end;

fun all_nondot_subdirs path = let
  val names = all_filenames_from_path path
  val names = List.filter (fn s => is_dir (path ^ "/" ^ s)) names
  val names = List.filter (not o String.isPrefix ".") names
  in names end

fun apply_in_all_dirs f path = let
  val _ = f path
  val dirs = map (fn n => path ^ "/" ^ n) (all_nondot_subdirs path)
  val _ = map (apply_in_all_dirs f) dirs
  in () end;

fun has_suffix [] n = false
  | has_suffix (suff::suffs) n =
      String.isSuffix suff n orelse has_suffix suffs n

fun source_files_in path = let
  val names = all_filenames_from_path path
  val names = List.filter (fn s => not (is_dir (path ^ "/" ^ s))) names
  val names = List.filter (not o String.isPrefix ".") names
  val names = List.filter (has_suffix AUTO_INCLUDE_SUFFIXES) names
  in names end

val had_error = ref false

fun lint_dir path = let
  val files = source_files_in path
  fun lint f = let
    val full = path ^ "/" ^ f
    in lint_file full
       handle LintExn msg =>
         (print ("ERROR in " ^ full ^ ": " ^ msg ^ "\n");
          had_error := true)
    end
  in List.app lint files end

fun lint_all path = let
  val _ = had_error := false
  val _ = apply_in_all_dirs lint_dir path
  in if !had_error
     then (err "Linting failed with errors above."; ())
     else print "Linting passed.\n"
  end

(* Main entry point *)

fun main () =
  let
    val args = CommandLine.arguments ()
  in
    case args of
      ["--all"] => lint_all (OS.FileSys.getDir())
    | ("--all" :: path :: _) => lint_all path
    | [] => (err "Usage: lint_source [--all [path] | file1 file2 ...]"; ())
    | [path] =>
        if is_dir path then
          (had_error := false;
           lint_dir path;
           if !had_error
           then (err "Linting failed with errors above."; ())
           else ())
        else let
          val _ = had_error := false
          val _ = lint_file path
                  handle LintExn msg =>
                    (print ("ERROR in " ^ path ^ ": " ^ msg ^ "\n");
                     had_error := true)
          in if !had_error
             then (err "Linting failed with errors above."; ())
             else ()
          end
    | files => let
        val _ = had_error := false
        fun lint f =
          lint_file f
          handle LintExn msg =>
            (print ("ERROR in " ^ f ^ ": " ^ msg ^ "\n");
             had_error := true)
        val _ = List.app lint files
        in if !had_error
           then (err "Linting failed with errors above."; ())
           else ()
        end
  end;
