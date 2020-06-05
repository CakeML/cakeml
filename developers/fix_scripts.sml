
val new_str = "val _ = temp_delsimps [\"NORMEQ_CONV\"]\n\n"

fun mem x [] = false | mem x (y::ys) = x = y orelse mem x ys;
fun fst (x,y) = x
fun snd (x,y) = y

fun read_all f x =
  case f x of NONE => [] | SOME y => y :: read_all f x

fun get_all_fails holmake_output_filename = let
  val f = TextIO.openIn holmake_output_filename
  val xs = read_all TextIO.inputLine f
  val _ = TextIO.closeIn f
  fun is_fail_line s =
    String.isSubstring "FAIL" s andalso
    String.isSubstring "user" s andalso
    String.isSubstring "real" s;
  in map (hd o String.tokens (fn c => c = #" ")) (List.filter is_fail_line xs) end

fun get_all_fail_scripts holmake_output_filename = let
  val zs = get_all_fails holmake_output_filename
  val zs = List.filter (String.isSuffix "Theory") zs
  fun g s = String.substring(s,0,size s - 6) ^ "Script.sml"
  in map g zs end

fun diff xs ys = List.filter (fn x => not (mem x ys)) xs;
fun inter xs ys = List.filter (fn x => mem x ys) xs;

fun find_all to_find path = let
  val d = OS.FileSys.openDir path
  val content = read_all OS.FileSys.readDir d
  val content = List.filter (not o String.isPrefix ".") content
  val found = inter to_find content
  val to_find = diff to_find found
  val found = map (fn s => (s,path ^ "/" ^ s)) found
  val content = diff content to_find
  val subdirs = List.filter OS.FileSys.isDir (map (fn s => path ^ "/" ^ s) content)
  val res = List.concat (found :: map (find_all to_find) subdirs)
  in res end

fun rec_find_all to_find path =
  if null to_find then [] else
  let
    val fs = find_all to_find path
    val found = map fst fs
    val names = map snd fs
    val to_find = diff to_find found
  in
    names @ rec_find_all to_find (path ^ "/..")
  end

fun find_files to_find = let
  val paths = rec_find_all to_find "."
  fun f s = if String.isPrefix "./" s
            then String.substring(s, 2, size s - 2)
            else s
  in map f paths end;

fun patch filename = let
  val _ = print ("Patching " ^ filename ^ " ... ")
  val f = TextIO.openIn filename
  val s = TextIO.inputAll f
  val _ = TextIO.closeIn f
  in if String.isSubstring new_str s then
       print "WARNING: trying to patch twice!\n\n"
     else let
       val key = "new_theory"
       val l = size key
       fun find_index k i =
         if String.substring(s,i,l) = key then k else
         if String.substring(s,i,1) = "\n" then find_index i (i+1) else
           find_index k (i+1)
       val cut_point = find_index 0 0 + 1
       val prefix = String.substring(s,0,cut_point)
       val suffix = String.substring(s,cut_point,size s - cut_point)
       val new_s = String.concat [prefix, new_str, suffix]
       val f = TextIO.openOut filename
       val s = TextIO.output (f,new_s)
       val _ = TextIO.closeOut f
       val _ = print ("done.\n")
       in () end end

fun main () = let
  val filename = "fails"
  val _ = print "Running Holmake ... "
  val _ = OS.Process.system ("Holmake -j8 -k 2>&1 > " ^ filename)
  val _ = print "done.\n"
  val _ = print "Reading output. "
  val to_find = get_all_fail_scripts filename
  val _ = if null to_find then
            (print "No failures.\n"; OS.Process.exit OS.Process.success)
          else ()
  val _ = print ("Found " ^ Int.toString (List.length to_find) ^ " failures:\n")
  val _ = List.app (fn s => print (" - " ^ s ^ "\n")) to_find
  val to_find = find_files to_find
  val _ = List.app patch to_find
  in main () end;

val _ = main ();
