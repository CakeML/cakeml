(*
  This SML program performs sanity checks on `build-sequence` and
  `build-exludes`, and makes sure all directories that contain a Holmakefile
  are either built or explicitly excluded.
*)

(* Constants *)
val BUILD_SEQUENCE_PATH = "build-sequence"
val BUILD_EXCLUDES_PATH = "build-excludes"

(* Helper functions *)

(* Returns the lines of a file as a list of strings, excluding the terminating
   newline character. *)
fun read_lines (filename : string) : string list =
  let
    val f = TextIO.openIn(filename)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line =>
        (* Drop newline character at the end of every line *)
        let val line = substring (line, 0, ((size line) - 1))
        in if line = "" then read_rest () else line :: read_rest () end
    val all_lines = read_rest ()
    val _ = TextIO.closeIn f
  in all_lines end

(* Checks whether a line is not a comment, i.e., does not start with #. *)
fun is_not_comment (line : string) : bool =
  not (String.isPrefix "#" line)

(* Checks whether a string is a valid path to a directory. *)
fun is_not_directory (s : string) : bool =
  (* Exception occurs if s does not exist or if the directory in which s
     resides is not accessible *)
  not (OS.FileSys.isDir s) handle OS.SysErr (_,_) => true

(* Returns all elements in xs that are not in ys. *)
fun difference xs ys =
  List.filter (fn x => not (List.exists (fn y => y = x) ys)) xs

(* Counts the frequency of each element in the list. *)
fun count x [] = 0
  | count x (y::ys) =
    if x = y
    then 1 + count x ys
    else count x ys

(* Removes duplicates from the given list. *)
fun remove_duplicates [] = []
  | remove_duplicates (x::xs) =
    x :: remove_duplicates (List.filter (fn y => y <> x) xs)

(* Returns a list of all duplicated elements. *)
fun find_duplicates xs =
  List.filter (fn x => count x xs > 1) (remove_duplicates xs)

(* Converts the paths in a list to a string which lists the paths relative
 * to the CakeML root. *)
fun paths_to_string cml_root ps =
  let
    val relative_paths =
      List.map (fn p => (OS.Path.mkRelative {path = p, relativeTo = cml_root})) ps
  in String.concatWith "\n" relative_paths end

(* Raises an exception if the condition does not hold. *)
fun assert condition message =
  condition orelse raise Fail message

(* Check if the directory contains a Holmakefile. *)
fun contains_holmakefile dir =
  OS.FileSys.access(OS.Path.concat (dir, "Holmakefile"), [])

(* Returns a list of the current directory and all of its
 * subdirectories recursively.
 *
 * May do funky stuff in the presence of symbolic links and the like,
 * i.e., when the directory structure from ‘dir’ is not a tree. *)
fun subdirectories dir =
  let
    val dir_stream = OS.FileSys.openDir dir
    fun process_stream () =
      case OS.FileSys.readDir dir_stream of
        NONE => []
      | SOME filename =>
        let
          val full_path = OS.Path.concat (dir, filename)
        in
          if OS.FileSys.isDir full_path
          then (subdirectories full_path) @ process_stream ()
          else process_stream ()
        end
    val result = dir :: process_stream ()
    val _ = OS.FileSys.closeDir dir_stream
  in result end

(* Main functions *)

(* Returns the (unique) directories contained in the ‘build-sequence’ file. *)
fun parse_build_sequence cml_root =
  let
    (* Returns the path from a line.
     * Assumes the line can be described by the regex ‘path(:artefact)*’ *)
    fun path_from_line line =
      (* String.fields never returns an empty list, so this should be safe *)
      hd (String.fields (fn c => c = #":") line)
    val lines = read_lines BUILD_SEQUENCE_PATH
    val lines = List.filter is_not_comment lines
    val paths = List.map path_from_line lines
    val paths = List.map (fn p => OS.Path.concat (cml_root, p)) paths
    val invalid_paths = List.filter is_not_directory paths
    val _ = assert (invalid_paths = [])
                   ("The following lines are not valid directories:\n" ^
                    (paths_to_string cml_root invalid_paths))
    val duplicate_paths = find_duplicates paths
    val _ = assert (duplicate_paths = [])
                   ("Please remove the following duplicates:\n" ^
                    (paths_to_string cml_root duplicate_paths))
    val no_holmakefile_paths =
      List.filter (fn p => not (contains_holmakefile p)) paths
    val _ = assert (no_holmakefile_paths = [])
                   ("The following paths do not contain a Holmakefile:\n" ^
                    (paths_to_string cml_root no_holmakefile_paths))
  in List.map OS.FileSys.realPath paths end

(* Returns the (unique) directories contained in the ‘build-excludes’ file. *)
fun parse_build_excludes cml_root =
  let
    val lines = read_lines BUILD_EXCLUDES_PATH
    val paths = List.filter is_not_comment lines
    val paths = List.map (fn p => OS.Path.concat (cml_root, p)) paths
    val invalid_paths = List.filter is_not_directory paths
    val _ = assert (invalid_paths = [])
                   ("The following lines are not valid directories:\n" ^
                    (paths_to_string cml_root invalid_paths))
    val duplicate_paths = find_duplicates paths
    val _ = assert (duplicate_paths = [])
                   ("Please remove the following duplicates:\n" ^
                    (paths_to_string cml_root duplicate_paths))
    val no_holmakefile_paths =
      List.filter (fn p => not (contains_holmakefile p)) paths
    val _ = assert (no_holmakefile_paths = [])
                   ("The following paths do not contain a Holmakefile:\n" ^
                    (paths_to_string cml_root no_holmakefile_paths))
  in List.map OS.FileSys.realPath paths end

(* Returns a unique list of all directories reachable from the CakeML root that
 * contain a Holmakefile (potentially including the root). *)
fun potential_build_paths cml_root =
  let
    val build_paths =
      List.filter contains_holmakefile (subdirectories cml_root)
  in
    (* Not sure whether subdirectories guarantees a unique list, so we make
     * sure there are no duplicates. *)
    List.map OS.FileSys.realPath (remove_duplicates build_paths)
  end

(* Performs sanity checks on ‘build-sequence’ and ‘build-exludes’, and makes
 * sure all directories that contain a Holmakefile are either built or
 * explicitly excluded. *)
fun lint_build_directories cml_root =
  let
    val build_paths = parse_build_sequence cml_root
    val excluded_paths = parse_build_excludes cml_root
    val accounted_paths = build_paths @ excluded_paths
    val duplicated_paths = find_duplicates accounted_paths
    val _ = assert (duplicated_paths = [])
                   ("The following paths are mentioned in both build-sequence and build-excludes:\n" ^
                    (paths_to_string cml_root duplicated_paths) ^
                    "\nPlease place them in either one or the other.")
    val all_build_paths = potential_build_paths cml_root
    val unaccounted_paths = difference all_build_paths accounted_paths
    val _ = assert (unaccounted_paths = [])
                   ("The following paths are not mentioned in either build-sequence and build-excludes:\n" ^
                    (paths_to_string cml_root unaccounted_paths) ^
                    "\nPlease place them in either one or the other.")
  in () end

fun err msg = (print msg; print "\n"; OS.Process.exit OS.Process.failure)

(* Letting the user/Holmake pass in the CakeML root is (hopefully) less
 * brittle than taking the relative path using getDir and concat. *)
fun main () =
  let
    val args = CommandLine.arguments ()
    val _ = if List.length args <> 1
            then err "Usage: lint_build_dirs cakeml_root"
            else ()
    val cml_root = List.nth (args, 0)
    val _ = if is_not_directory cml_root
            then err (cml_root ^ " is not a valid directory.")
            else ()
  in
    lint_build_directories cml_root handle Fail msg => err msg
  end
