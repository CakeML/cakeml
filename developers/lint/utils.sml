(* Raises an exception if the condition does not hold. *)
fun assert condition message =
    condition orelse raise Fail message

(* Returns the lines of a stream as a list of strings, excluding the terminating
   newline character. *)
fun read_stream (stream : TextIO.instream) : string list =
    case TextIO.inputLine(stream) of
        NONE => []
      | SOME line =>
        let
          (* Drop newline character at the end of every line *)
          val line = substring (line, 0, ((size line) - 1))
        in
          if line = ""
          then read_stream stream
          else line :: (read_stream stream)
        end

(* Returns the lines of a file as a list of strings, excluding the terminating
   newline character. *)
fun read_lines (filename : string) : string list =
    let
      val f = TextIO.openIn(filename)
      val all_lines = read_stream f
      val _ = TextIO.closeIn f
    in all_lines end

(* Executes a shell command and returns its output as a list of strings. *)
fun run_cmd (cmd : string) : string list =
    let
      val proc = Unix.execute ("/bin/sh", ["-c", cmd])
      val output = read_stream (Unix.textInstreamOf proc)
      val status = Unix.reap proc
      val _ = assert (OS.Process.isSuccess status)
                     (cmd ^ " failed.")
    in output end

(* Checks whether a string is a valid path to a directory. *)
fun is_directory (s : string) : bool =
    (* Exception occurs if s does not exist or if the directory in which s
     * resides is not accessible *)
    (OS.FileSys.isDir s) handle OS.SysErr (_,_) => false

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

(* Check if the directory contains a Holmakefile. *)
fun directory_contains dir file =
    OS.FileSys.access (OS.Path.mkAbsolute {path = file, relativeTo = dir}, [])

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
          val full_path = OS.Path.mkAbsolute {path = filename, relativeTo = dir}
        in
          if OS.FileSys.isDir full_path
          then (subdirectories full_path) @ process_stream ()
          else process_stream ()
        end
    val result = dir :: process_stream ()
    val _ = OS.FileSys.closeDir dir_stream
  in result end
