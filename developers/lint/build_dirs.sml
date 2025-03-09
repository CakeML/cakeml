(*
  This SML program performs sanity checks on `build-sequence` and
  `build-exludes`, and makes sure all directories that contain a Holmakefile
  are either built or explicitly excluded.
*)

use "utils.sml"

(* Constants *)

val BUILD_SEQUENCE_PATH = "../build-sequence"
val BUILD_EXCLUDES_PATH = "../build-excludes"

(* Root of git repository = CakeML project root *)
val CAKEML_ROOT =
    let
      val cmd = "git rev-parse --show-toplevel"
      val output = run_cmd cmd
      val _ = assert (List.length output = 1)
                     ("'" ^ cmd ^ "' did not return exactly one line.")
      val output = List.hd output
      val _ = assert (is_directory output)
                     (output ^ " cannot be the CakeML root, since it is not a directory.")
    in output end

(* Consider only directories that are tracked by git *)
val CAKEML_DIRS =
    let
      val cmd = "git ls-tree --full-tree --name-only -r HEAD | xargs dirname | sort | uniq"
      val output = (run_cmd cmd)
      val paths = List.map (fn p => OS.Path.mkAbsolute {path = p, relativeTo = CAKEML_ROOT}) output
      val invalid = List.filter (fn s => not (is_directory s)) paths
      val _ = assert (invalid = [])
                     ("The following lines cannot be CakeML directories, since they aren't directories:\n" ^
                      (String.concatWith "\n" invalid))
    in paths end

(* Helpers *)

(* Checks whether a line is not a comment, i.e., does not start with #. *)
fun is_not_comment (line : string) : bool =
  not (String.isPrefix "#" line)

(* Converts the paths in a list to a string which lists the paths relative
 * to the CakeML root. *)
fun to_relative_string (ps : string list) : string =
  let
    val relative_paths =
      List.map (fn p => (OS.Path.mkRelative {path = p, relativeTo = CAKEML_ROOT})) ps
  in String.concatWith "\n" relative_paths end

(* Main functions *)

(* Returns the (unique) directories contained in the ‘build-sequence’ file. *)
fun parse_build_sequence () : string list =
  let
    (* Returns the path from a line.
     * Assumes the line can be described by the regex ‘path(:artefact)*’ *)
    fun path_from_line line =
      (* String.fields never returns an empty list, so this should be safe *)
      hd (String.fields (fn c => c = #":") line)
    val lines = read_lines BUILD_SEQUENCE_PATH
    val lines = List.filter is_not_comment lines
    val paths = List.map path_from_line lines
    val paths = List.map (fn p => OS.Path.mkAbsolute {path = p, relativeTo = CAKEML_ROOT}) paths
    val invalid_paths = List.filter (fn dir => not (is_directory dir)) paths
    val _ = assert (invalid_paths = [])
                   ("The following lines in build-sequence are not valid directories:\n" ^
                    (to_relative_string invalid_paths))
    val duplicate_paths = find_duplicates paths
    val _ = assert (duplicate_paths = [])
                   ("Please remove the following duplicates from build-sequence:\n" ^
                    (to_relative_string duplicate_paths))
    val no_holmakefile_paths =
      List.filter (fn p => not (directory_contains p "Holmakefile")) paths
    val _ = assert (no_holmakefile_paths = [])
                   ("The following paths in build-sequence do not contain a Holmakefile:\n" ^
                    (to_relative_string no_holmakefile_paths))
  in List.map OS.FileSys.realPath paths end

(* Returns the (unique) directories contained in the ‘build-excludes’ file. *)
fun parse_build_excludes () =
  let
    val lines = read_lines BUILD_EXCLUDES_PATH
    val paths = List.filter is_not_comment lines
    val paths = List.map (fn p => OS.Path.mkAbsolute {path = p, relativeTo = CAKEML_ROOT}) paths
    val invalid_paths = List.filter (fn dir => not (is_directory dir)) paths
    val _ = assert (invalid_paths = [])
                   ("The following lines in build-excludes are not valid directories:\n" ^
                    (to_relative_string invalid_paths))
    val duplicate_paths = find_duplicates paths
    val _ = assert (duplicate_paths = [])
                   ("Please remove the following duplicates from build-excludes:\n" ^
                    (to_relative_string duplicate_paths))
    val no_holmakefile_paths =
      List.filter (fn p => not (directory_contains p "Holmakefile")) paths
    val _ = assert (no_holmakefile_paths = [])
                   ("The following paths in build-excludes do not contain a Holmakefile:\n" ^
                    (to_relative_string no_holmakefile_paths))
  in List.map OS.FileSys.realPath paths end

(* Performs sanity checks on ‘build-sequence’ and ‘build-excludes’, and makes
 * sure all directories that contain a Holmakefile are either built or
 * explicitly excluded. *)
fun lint_build_directories () =
  let
    val build_paths = parse_build_sequence ()
    val excluded_paths = parse_build_excludes ()
    val accounted_paths = build_paths @ excluded_paths
    val duplicated_paths = find_duplicates accounted_paths
    val _ = assert (duplicated_paths = [])
                   ("The following paths are mentioned in both build-sequence and build-excludes:\n" ^
                    (to_relative_string duplicated_paths) ^
                    "\nPlease place them in either one or the other.")
    val potential_build_paths = List.filter (fn p => directory_contains p "Holmakefile") CAKEML_DIRS
    val unaccounted_paths = difference potential_build_paths accounted_paths
    val _ = assert (unaccounted_paths = [])
                   ("The following paths are not mentioned in either build-sequence and build-excludes:\n" ^
                    (to_relative_string unaccounted_paths) ^
                    "\nPlease place them in either one or the other.")
  in () end

fun err msg = (print msg; print "\n"; OS.Process.exit OS.Process.failure)

fun main () =
  let
    val args = CommandLine.arguments ()
    val _ = if List.length args <> 0
            then err "lint_build_dirs does not take arguments."
            else ()
  in
    lint_build_directories () handle Fail msg => err msg
  end
