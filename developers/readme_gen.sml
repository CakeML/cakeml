(*
   This SML program generates a `README.md` summary for the files
   given as command-line arguments to this script. The contents of the
   summaries are read from a specific style of comment that needs to
   appear at the top of each file.

   This program accepts a command-line option --check which performs a
   recursive check of all of the subdirectories. The global check
   checks that:
    - there is a README.md target in every Holmakefile
    - in dirs without a Holmakefile,
       - there must be a README.md
       - there must not be any Script.sml files
    - in dirs with a Holmakefile
       - there must be a readmePrefix file
       - the first target in the Holmakefile must have the following
         as a prefix "all: $(DEFAULT_TARGETS) README.md"
       - create_summary must work in the dir (doesn't writing output)
*)

(* Constants *)

val MAX_CHAR_COUNT_PER_LINE = 80
val MAX_LINE_COUNT = 10
val MAX_CODE_LINE_LENGTH = 200
val PREFIX_FILENAME = "readmePrefix"
val OUTPUT_FILENAME = "README.md"
val CHECK_OPT = "--check"
val AUTO_INCLUDE_SUFFIXES = ["Script.sml","Syntax.sml","Lib.sml",".lem",".c",".cml"]
val FIRST_TARGET_PREFIX = "all: $(DEFAULT_TARGETS) README.md"

val HOLMAKEFILE_SUGGESTION =
 concat ["README_SOURCES = $(wildcard *Script.sml) $(wildcard *Lib.sml) ",
         "$(wildcard *Syntax.sml)\n",
         "DIRS = $(wildcard */)\n",
         "README.md: $(CAKEMLDIR)/developers/readme_gen",
         " readmePrefix $(patsubst %,%readmePrefix,$(DIRS)) $(README_SOURCES)\n",
         "\t$(CAKEMLDIR)/developers/readme_gen $(README_SOURCES)\n"]

val ILLEGAL_STRINGS =
  [("store_thm(\"", "The Theorem syntax is to be used instead of store_thm."),
   ("type_abbrev(\"", "The Type syntax is to be used instead of type_abbrev."),
   ("overload_on(\"", "Use Overload ... = ``...`` instead of overload_on."),
   ("Hol_datatype"^"`", "Use Datatype: ... End syntax instead of Hol_datatype."),
   ("Hol_rel"^"n`","Use Inductive ... End instead of old Hol_reln."),
   ("Hol_rel"^"n\"","Use Inductive ... End instead of old Hol_reln."),
   ("Hol_corel"^"n`","Use CoInductive ... End instead of old Hol_coreln.")]

(* Helper functions *)

exception ReadmeExn of string;

fun fail str = raise ReadmeExn str;

fun err s = (print s; print "\n"; OS.Process.exit OS.Process.failure; false);

fun comma [] = ""
  | comma [x] = x
  | comma (x::xs) = x ^ ", " ^ comma xs;

fun every_char p str = List.all p (explode str);

fun exists_char p str = List.exists p (explode str);

fun equal x y = x = y

fun mem x [] = false
  | mem x (y::ys) = if x = y then true else mem x ys;

fun distinct [] = []
  | distinct (x::xs) = x :: distinct (List.filter (fn y => x <> y) xs)

val is_blank_line = every_char Char.isSpace;

fun take_while p [] = []
  | take_while p (x::xs) = if p x then x :: take_while p xs else [];

fun drop_while p [] = []
  | drop_while p (x::xs) = if p x then drop_while p xs else x::xs;

fun drop_chars n str = Substring.string (Substring.triml n (Substring.full str));

fun check_length all_lines = let
  val _ = length all_lines <= MAX_LINE_COUNT orelse
          fail ("first comment must be at most " ^ Int.toString MAX_LINE_COUNT ^ " lines long")
  in () end

fun check_width all_lines = let
  val _ = List.all (fn line => String.size line <= MAX_CHAR_COUNT_PER_LINE) all_lines orelse
          fail ("one or more lines exceed the line length limit of " ^ Int.toString MAX_CHAR_COUNT_PER_LINE ^ " characters")
  in () end

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

fun check_length_and_width all_lines =
  (check_length all_lines; check_width all_lines);

fun open_textfile filename =
  TextIO.openIn(filename)
  handle IO.Io _ => fail ("unable to open file: " ^ filename);

fun write_file filename content = let
  val f = TextIO.openOut(filename)
  val _ = TextIO.output(f,content)
  val _ = TextIO.closeOut f
  in content end

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

(* Reading a block comment (from an SML or C file) *)

fun read_block_comment start_comment end_comment filename = let
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
  val _ = every_line_in_file filename
            (fn n => fn line => ( assert_no_trailing_whitespace n line ;
                                  assert_no_tabs_in_line n line ;
                                  assert_line_length_OK n line ))
  val _ = check_for_illegal_strings filename (read_all_lines filename)
  val f = open_textfile filename
  in let
    (* check that first line is comment *)
    fun comm_fail () = fail ("file must start with " ^ start_comment)
    val hd_line = (case TextIO.inputLine(f) of
                     NONE => comm_fail ()
                   | SOME line => line);
    val _ = String.isPrefix start_comment hd_line orelse comm_fail ()
    in if String.isSubstring " - generated by L3 - " hd_line then
         ["An instruction set model generated from Anthony Fox's L3 tool."]
       else let
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
    val _ = TextIO.closeIn(f)
    in all_lines end handle e => (TextIO.closeIn(f); raise e)
  end end;

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
    val _ = TextIO.closeIn(f)
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
    val _ = TextIO.closeIn(f)
    in all_lines end handle e => (TextIO.closeIn(f); raise e)
  end;

(* Read from a markdown file, e.g. how-to.md *)

(*
val filename = "../how-to.md"
*)
fun read_comment_from_markdown filename = let
  val lines = Option.valOf (read_all_lines filename)
  val line = List.nth (lines,1) handle Subscript => "\n"
  val line2 = List.nth (lines,2) handle Subscript => "\n"
  val lines = if String.isPrefix "==" line orelse String.isPrefix "--" line
              then List.drop(lines,if is_blank_line line2 then 3 else 2)
              else lines
  fun take_until p [] = []
    | take_until p (x::xs) = if p x then [] else x :: take_until p xs
  fun drop_until p [] = []
    | drop_until p (x::xs) = if p x then x::xs else drop_until p xs
  fun until_next_blank_line [] = []
    | until_next_blank_line (x::xs) =
        if is_blank_line x then [] else
        if String.isSuffix ":\n" x then
          x :: take_until (not o is_blank_line) xs
          @ until_next_blank_line (drop_until (not o is_blank_line) xs)
        else x :: until_next_blank_line xs
  in until_next_blank_line lines end;

(* Read first paragraph of header from directory *)

fun file_exists filename =
  let
    val f = TextIO.openIn(filename)
    val _ = TextIO.closeIn f
  in true end handle e => false;

fun read_comment_from_dir path = let
  val _ = (OS.FileSys.isDir path handle OS.SysErr _ => false)
          orelse fail "this is not a directory"
  val path = if String.isSuffix "/" path then path else path ^ "/"
  in if file_exists (path ^ "Holmakefile") then
       read_comment_from_raw (path ^ PREFIX_FILENAME)
     else
       read_comment_from_raw (path ^ OUTPUT_FILENAME) end

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

(* Functions about directories *)

fun all_filenames_from_path path = let
  val d = OS.FileSys.openDir(path)
  fun all () =
    case OS.FileSys.readDir(d) of
      NONE => [] | SOME name => name :: all ()
  val names = all ()
  val _ = OS.FileSys.closeDir(d)
  in names end;

fun is_dir filename =
  OS.FileSys.isDir filename handle OS.SysErr _ => false;

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

fun auto_include_filenames path = let
  val names = all_filenames_from_path path
  val dirs = List.filter (fn s => is_dir (path ^ "/" ^ s)) names
  val dirs = List.filter (not o String.isPrefix ".") dirs
  val names = List.filter (fn s => not (is_dir (path ^ "/" ^ s))) names
  val names = List.filter (not o String.isPrefix ".") names
  fun has_suffix [] n = false
    | has_suffix (suff::suffs) n =
        String.isSuffix suff n orelse has_suffix suffs n
  val names = List.filter (has_suffix AUTO_INCLUDE_SUFFIXES) names
  in names @ dirs end

(*
val SOME lines = read_all_lines filename
*)

fun check_Holmakefile filename =
  case read_all_lines filename of
    NONE => err ("Unable to read: " ^ filename)
  | SOME lines => let
      val _ = List.exists (fn s => String.isPrefix (OUTPUT_FILENAME ^ ":") s) lines
              orelse (err (concat
                ["ERROR! Every Holmakefile must include a ", OUTPUT_FILENAME,
                 " target. Consider adding:\n\n",HOLMAKEFILE_SUGGESTION,
                 "\nto ",filename,"\n"]))
      fun is_target_line line = length (String.tokens (fn c => c = #":") line) > 1
      val xs = take_while (not o is_target_line) lines
      val ys = drop_while (not o is_target_line) lines
      val first_target = List.nth(ys,0)
      val _ = String.isPrefix FIRST_TARGET_PREFIX first_target
              orelse err (concat
                ["ERROR! The first target line must have\n\n",
                 FIRST_TARGET_PREFIX,"\n\nas a prefix in ", filename, "\n"])
           (* let
                val lines = List.filter (fn s => s <> "all: README.md\n") lines
                val xs = take_while (String.isSubstring "=") lines
                val ys = drop_while (String.isSubstring "=") lines
                val all_lines = xs @ ["\nall: $(DEFAULT_TARGETS) README.md\n"] @ ys
                val _ = write_file filename (concat all_lines)
              in true end *)
      in true end

(* Main functions: processing a list of files / paths *)

datatype res = TitleAndContent of string * (string list)
             | Error of string * string
             | Prefix of string list

fun isError (Error _) = true | isError _ = false;

fun create_summary write_output path extra_files = let
  val _ = check_Holmakefile (path ^ "/Holmakefile")
  val filenames = all_nondot_subdirs path @
                  auto_include_filenames path @ extra_files
  val filenames = sort (fn s1 => fn s2 => s1 <= s2) filenames
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
  fun do_filename filename = let
    val path_file = path ^ "/" ^ filename
    in if is_dir path_file then
         TitleAndContent (filename,read_comment_from_dir path_file)
       else if String.isSuffix ".sml" filename orelse
               String.isSuffix ".cml" filename orelse
               String.isSuffix ".lem" filename then
         TitleAndContent (filename,read_comment_from_sml path_file)
       else if String.isSuffix ".c" filename orelse
               String.isSuffix ".css" filename then
         TitleAndContent (filename,read_comment_from_c path_file)
       else if String.isSuffix ".sh" filename then
         TitleAndContent (filename,read_comment_from_script path_file)
       else if String.isSuffix ".md" filename then
         TitleAndContent (filename,read_comment_from_markdown path_file)
       else
         (TitleAndContent (filename,read_comment_from_script path_file)
          handle ReadmeExn msg =>
          TitleAndContent (filename,read_comment_from_raw path_file))
    end
    handle ReadmeExn msg => Error (filename,msg)
  val output = header :: map do_filename filenames
  (* check and report errors *)
  val _ = if List.exists isError output then let
            val _ = print ("ERROR! readme_gen.sml failed due to:\n")
            fun print_err (Error (name,msg)) =
                  print (name ^ ": " ^ msg ^ "\n")
              | print_err _ = ()
            val _ = map print_err output
            val _ = err ("These errors were in: " ^ path ^ "\n")
            in () end
          else ()
  (* generate output *)
  val _ = if not write_output then () else
            let
              val f = TextIO.openOut(OUTPUT_FILENAME)
              fun write_line str = TextIO.output(f,str)
              fun write_item (Prefix lines) = (map write_line lines; ())
                | write_item (Error _) = ()
                | write_item (TitleAndContent (title,lines)) =
                    (write_line ("\n[" ^ title ^ "](" ^ title ^ "):\n") ;
                     map write_line lines; ())
              val _ = map write_item output
              val _ = TextIO.closeOut(f)
            in () end
  in () end;

(* Recursive check of all dirs *)

fun assert_for_lines_of filename pred err_msg =
  (pred (read_all_lines filename) handle _ => false)
  orelse err (err_msg filename);

fun run_full_check path = let
  fun remove_prefix prefix s =
    if String.isPrefix prefix s then
      String.substring(s,String.size prefix,String.size s - String.size prefix)
    else s
  fun show_path p =
    if p = path then "." else remove_prefix (path ^ "/") p
  fun common_prefix s t = let
    fun common (x::xs) (y::ys) = if x = y then x::(common xs ys) else []
      | common _ _ = []
    in implode (common (explode s) (explode t)) end
  fun inject_readme_target p [] = ["\n",HOLMAKEFILE_SUGGESTION]
    | inject_readme_target p (l::ls) =
        if String.isPrefix "ifdef" l orelse String.isPrefix "ifndef" l then
          [HOLMAKEFILE_SUGGESTION,"\n"] @ l::ls
        else l :: inject_readme_target p ls
(*
  val p = path
  val SOME lines = read_all_lines (p ^ "/Holmakefile")
*)
  fun check_dir p =
    case read_all_lines (p ^ "/Holmakefile") of
      NONE => (* case: Holmake file does not exist *)
        let
          (* prefix file must not exist *)
          val _ = assert_for_lines_of (p ^ "/" ^ PREFIX_FILENAME)
                    (not o Option.isSome)
                    (fn s => "File not allowed to exist: " ^ s ^ "\n" ^
                             "Such files are only allowed in directories " ^
                             "with a Holmakefile.\nFix: rename the file to " ^
                             OUTPUT_FILENAME)
          (* README.md file must exist *)
          val _ = assert_for_lines_of (p ^ "/" ^ OUTPUT_FILENAME)
                    Option.isSome
                    (fn s => "Missing file: " ^ s ^ "\n" ^
                             "Write the file! " ^
                             "It is not automatically generated due to lack "^
                             "of a Holmakefile.")
        in () end
    | SOME lines => (* case: Holmake file exists *)
        let
          val _ = print ("Checking: " ^ p ^ "\n")
          (* prefix file must exist *)
          val _ = assert_for_lines_of (p ^ "/" ^ PREFIX_FILENAME)
                    Option.isSome (fn s => "Missing file: " ^ s)
          (* attempt to build readme without writing the file, because the
             Holmakefile might be set up to include extra_files via
             command-line arguments to readme_gen *)
          val extra_files = ([]:string list)
          val write_output = false
          val _ = create_summary write_output p extra_files
        in () end
  val _ = apply_in_all_dirs check_dir path
  in () end;

(* Main entry point *)

fun main () =
  let
    val args = CommandLine.arguments ()
    val extra_files = args
    val path = OS.FileSys.getDir()
    val write_output = true
  in
    if List.length args <> 0 andalso List.nth(args,0) = CHECK_OPT
    then run_full_check (if length args > 1 then List.nth(args,1) else path)
    else create_summary write_output path extra_files
  end;
