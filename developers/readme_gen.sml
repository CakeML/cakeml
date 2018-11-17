(*
   This SML program generates a `README.md` summary for the files
   given as command-line arguments to this script. The contents of the
   summaries are read from a specific style of comment that needs to
   appear at the top of each given file.
*)

(* Constants *)

val MAX_CHAR_COUNT_PER_LINE = 80
val MAX_LINE_COUNT = 10
val PREFIX_FILENAME = "readmePrefix"
val OUTPUT_FILENAME = "README.md"
val CHECK_OPT = "--check"

(* Helper functions *)

exception ReadmeExn of string;

fun fail str = raise ReadmeExn str;

fun every_char p str = List.all p (explode str);

fun exists_char p str = List.exists p (explode str);

fun equal x y = x = y

fun distinct [] = []
  | distinct (x::xs) = x :: distinct (List.filter (fn y => x <> y) xs)

val is_blank_line = every_char Char.isSpace;

fun take_while p [] = []
  | take_while p (x::xs) = if p x then x :: take_while p xs else [];

fun drop_chars n str = Substring.string (Substring.triml n (Substring.full str));

fun check_length all_lines = let
  val _ = length all_lines <= MAX_LINE_COUNT orelse
          fail ("first comment must be at most " ^ Int.toString MAX_LINE_COUNT ^ " lines long")
  in () end

fun check_width all_lines = let
  val _ = List.all (fn line => String.size line <= MAX_CHAR_COUNT_PER_LINE) all_lines orelse
          fail ("one or more lines exceed the line length limit of " ^ Int.toString MAX_CHAR_COUNT_PER_LINE ^ " characters")
  in () end

fun check_length_and_width all_lines =
  (check_length all_lines; check_width all_lines);

fun open_textfile filename =
  TextIO.openIn(filename)
  handle IO.Io _ => fail ("unable to open file: " ^ filename);

fun sort P = (* copied from HOL *)
   let
      fun merge [] a = a
        | merge a [] = a
        | merge (A as (a :: t1)) (B as (b :: t2)) =
             if P a b then a :: merge t1 B
                      else b :: merge A t2
      fun srt [] = []
        | srt [a] = a
        | srt (h1 :: h2 :: t) = srt (merge h1 h2 :: t)
   in
      srt o (map (fn x => [x]))
   end

(* Reading a block comment (from an SML or C file) *)

fun read_block_comment start_comment end_comment filename = let
  val f = open_textfile filename
  in let
    (* check that first line is comment *)
    fun comm_fail () = fail ("file must start with " ^ start_comment)
    val hd_line = (case TextIO.inputLine(f) of
                     NONE => comm_fail ()
                   | SOME line => line);
    val _ = String.isPrefix start_comment hd_line orelse comm_fail ()
    val _ = every_char (not o Char.isAlphaNum) hd_line orelse
              fail "first line must not contain alpha numberic chars"
    val _ = not (String.isSubstring end_comment hd_line) orelse
              fail ("first line must not contain " ^ end_comment)
    (* read first line of comment content *)
    val fst_line = (case TextIO.inputLine(f) of
                      NONE => fail "unable to read content of comment"
                    | SOME line =>
                        if is_blank_line line then
                          (case TextIO.inputLine(f) of
                             NONE => fail "unable to read content of comment"
                           | SOME line => line)
                        else line);
    val _ = not (is_blank_line fst_line) orelse
            fail "first content line must not be blank"
    val _ = exists_char Char.isAlphaNum fst_line orelse
            fail "first content line does not have alphanumeric chars"
    val _ = not (String.isSubstring end_comment fst_line) orelse
              fail ("first content line must not contain " ^ end_comment)
    val blank_prefix = implode (take_while (equal #" ") (explode fst_line))
    (* read rest of comment content *)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line =>
          if is_blank_line line then []
          else if String.isSubstring end_comment line then
            (if exists_char Char.isAlphaNum line then
               fail "first comment must end on line without alphanumeric chars"
             else [])
          else if String.isPrefix blank_prefix line then
            line :: read_rest ()
          else fail ("lines following first content line must not have less indentation; error at: " ^ line)
    val all_lines =
      map (drop_chars (String.size blank_prefix)) (fst_line :: read_rest ())
    val _ = check_length_and_width all_lines
    in all_lines end handle e => (TextIO.closeIn(f); raise e)
  end;

val read_comment_from_sml = read_block_comment "(*" "*)";
val read_comment_from_c = read_block_comment "/*" "*/";

(* Reading a comment from a shell-script file *)

fun read_comment_from_script filename = let
  val f = open_textfile filename
  val prefix = "## "
  val shebang = "#!"
  in let
    (* read the first line, ignore a shebang line *)
    val fst_line = (case TextIO.inputLine(f) of
                      NONE => fail "unable to read content of comment"
                    | SOME line =>
                        if String.isPrefix shebang line then
                          (case TextIO.inputLine(f) of
                             NONE => fail "unable to read content of comment"
                           | SOME line => line)
                        else line);
    val _ = String.isPrefix prefix fst_line orelse
            fail ("first line (after optional "^shebang^") did not have '" ^ prefix ^ "' as prefix")
    (* read rest of comment content *)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line =>
          if String.isPrefix prefix line then
            line :: read_rest ()
          else []
    val all_lines =
      map (drop_chars (String.size prefix)) (fst_line :: read_rest ())
    val _ = check_length_and_width all_lines
    in all_lines end handle e => (TextIO.closeIn(f); raise e)
  end;

(* Read from a raw text file, e.g. COPYING *)

fun read_comment_from_raw filename = let
  val f = open_textfile filename
  in let
    (* read lines until blank line *)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line => if is_blank_line line then [] else line :: read_rest ()
    val all_lines = read_rest ()
    val _ = all_lines <> [] orelse fail "no content on first line"
    val _ = exists_char Char.isAlphaNum (hd all_lines) orelse
            fail "first line must contain alphanumeric chars"
    val _ = not (String.isPrefix " " (hd all_lines)) orelse
            fail "first line must not start with a blank"
    val _ = check_length_and_width all_lines
    in all_lines end handle e => (TextIO.closeIn(f); raise e)
  end;

(* Read first paragraph of header from directory *)

fun read_comment_from_dir path = let
  val _ = (OS.FileSys.isDir path handle OS.SysErr _ => false)
          orelse fail "this is not a directory"
  val path = if String.isSuffix "/" path then path else path ^ "/"
  in read_comment_from_raw (path ^ PREFIX_FILENAME) end

(* Read full header file from directory *)

fun read_readme_prefix filename = let
  val f = open_textfile filename
  fun lines aux = case TextIO.inputLine(f) of
                    NONE => rev aux
                  | (SOME line) => lines (line::aux)
  val all_lines = lines []
  val _ = TextIO.closeIn(f)
  val _ = check_width all_lines
  val _ = all_lines <> [] orelse fail "no content on first line"
  in all_lines end;

(* Main functions: processing a list of files / paths *)

datatype res = TitleAndContent of string * (string list)
             | Error of string * string
             | Prefix of string list

fun isError (Error _) = true | isError _ = false;

fun create_summary filenames_and_paths = let
  val filenames = sort (fn s1 => fn s2 => s1 <= s2) filenames_and_paths
  val filenames = distinct filenames
  (* remove lem generated script files *)
  fun is_lem_generated filename =
    if String.isSuffix "Script.sml" filename then let
      val str = String.substring(filename,0,String.size(filename)-10)
      in List.exists (equal (str ^ ".lem")) filenames end
    else false
  val filenames = List.filter (not o is_lem_generated) filenames
  (* read what needs to come first in the output *)
  val filename = PREFIX_FILENAME
  val header = Prefix (read_readme_prefix filename)
               handle ReadmeExn msg => Error (filename, msg)
  (* process each filename *)
  fun do_filename filename =
    (if (OS.FileSys.isDir filename handle OS.SysErr _ => false) then
       TitleAndContent (filename,read_comment_from_dir filename)
     else if String.isSuffix ".sml" filename orelse
             String.isSuffix ".lem" filename then
       TitleAndContent (filename,read_comment_from_sml filename)
     else if String.isSuffix ".c" filename orelse
             String.isSuffix ".css" filename then
       TitleAndContent (filename,read_comment_from_c filename)
     else if String.isSuffix ".sh" filename then
       TitleAndContent (filename,read_comment_from_script filename)
     else
       (TitleAndContent (filename,read_comment_from_script filename)
        handle ReadmeExn msg =>
        TitleAndContent (filename,read_comment_from_raw filename)))
    handle ReadmeExn msg => Error (filename,msg)
  val output = header :: map do_filename filenames
  (* check and report errors *)
  val _ = if List.exists isError output then let
            val _ = print ("ERROR! readme_gen.sml cannot produce " ^
                           OUTPUT_FILENAME ^ " due to:\n")
            fun print_err (Error (name,msg)) =
                  print (name ^ ": " ^ msg ^ "\n")
              | print_err _ = ()
            val _ = map print_err output
            val _ = OS.Process.exit(OS.Process.failure)
            in () end
          else ()
  (* generate output *)
  val f = TextIO.openOut(OUTPUT_FILENAME)
  fun write_line str = TextIO.output(f,str)
  fun write_item (Prefix lines) = (map write_line lines; ())
    | write_item (Error _) = ()
    | write_item (TitleAndContent (title,lines)) =
        (write_line ("\n[" ^ title ^ "](" ^ title ^ "):\n") ;
         map write_line lines; ())
  val _ = map write_item output
  val _ = TextIO.closeOut(f)
  in () end;

fun all_nondot_subdirs path = let
  val d = OS.FileSys.openDir(path)
  fun all () =
    case OS.FileSys.readDir(d) of
      NONE => [] | SOME name => name :: all ()
  val names = all ()
  val _ = OS.FileSys.closeDir(d)
  val names = List.filter (fn n => OS.FileSys.isDir(path ^ "/" ^ n)
                                   handle OS.SysErr _ => false) names
  val names = List.filter (not o String.isPrefix ".") names
  in names end

fun all_dirs f path = let
  val _ = f path
  val dirs = map (fn n => path ^ "/" ^ n) (all_nondot_subdirs path)
  val _ = map (all_dirs f) dirs
  in () end;

(*
fun produce_readme_for_path path = 0;
*)

fun err s = (print s; print "\n"; OS.Process.exit OS.Process.failure; false);

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

fun assert_for_lines_of filename pred err_msg =
  (pred (read_all_lines filename) handle _ => false)
  orelse err (err_msg filename);

fun run_full_check () = let
  val path = OS.FileSys.getDir()
  val curr_dir = "developers"
  val _ = String.isSuffix curr_dir path orelse
          err ("The " ^ CHECK_OPT ^ " option can only be run in the "
                      ^ curr_dir ^ " dir.")
  val path = String.substring(path,0,size path - size curr_dir - 1)
  fun remove_prefix prefix s =
    if String.isPrefix prefix s then
      String.substring(s,String.size prefix,String.size s - String.size prefix)
    else s
  fun show_path p =
    if p = path then "." else remove_prefix (path ^ "/") p
  fun check_dir p =
    case read_all_lines (p ^ "/Holmakefile") of
      NONE => ()
    | SOME lines =>
        let
          val _ = assert_for_lines_of (p ^ "/" ^ PREFIX_FILENAME)
                    Option.isSome (fn s => "Missing file: " ^ s)
          val _ = List.exists (fn s => String.isPrefix (OUTPUT_FILENAME ^ ":") s)
                    lines (* orelse err ("No README target in " ^ p ^ "/Holmakefile") *)
        in () end
  in all_dirs check_dir path end;

fun mem x [] = false
  | mem x (y::ys) = if x = y then true else mem x ys;

fun main () = let
  val args = CommandLine.arguments ()
  val path = OS.FileSys.getDir()
  val dirs = all_nondot_subdirs path
  val _ = if mem CHECK_OPT args
          then run_full_check ()
          else create_summary (args @ dirs)
  in () end;
