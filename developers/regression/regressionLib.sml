(*
  Code shared between the pieces of the regression test suite.

  We use the filesystem as a database and put all state in it.
  Everything is relative to the current directory.

  We expect to be single-threaded, and use a lock file called
    lock
  to ensure this.

  API requests are expected via CGI environment variables.

  Job lists are implemented as three directories:
    waiting, active, stopped

  Jobs are implemented as files with their id as filename.

  The directory a job is in indicates its status.

  File contents for a job:
    - HOL and CakeML commits
    - optional worker name and start time
    - output
  More concretely:
    CakeML: <SHA>
      <short message> (<date>)
    [#<PR> (<PR-name>)
     Merging into: <SHA>
      <short message> (<date>)]
    HOL: <SHA>
      <short message> (<date>)
    [Machine: <worker name>
     Claimed: <date>]
    <date>: <line(s) of output>
    ...
*)

structure regressionLib = struct

fun equal x y = x = y

fun assoc k [] = raise Match
  | assoc k ((k',v)::ls) = if k = k' then v else assoc k ls

fun find f (x::xs) = if f x then x else find f xs
  | find _ _ = raise Match

fun max n m = if n < m then m else n

local
  fun maxl acc [] = acc
    | maxl acc (n::ns) = maxl (max acc n) ns
in val max_list = maxl 0 end

fun month_from_int 1 = Date.Jan
  | month_from_int 2 = Date.Feb
  | month_from_int 3 = Date.Mar
  | month_from_int 4 = Date.Apr
  | month_from_int 5 = Date.May
  | month_from_int 6 = Date.Jun
  | month_from_int 7 = Date.Jul
  | month_from_int 8 = Date.Aug
  | month_from_int 9 = Date.Sep
  | month_from_int 10 = Date.Oct
  | month_from_int 11 = Date.Nov
  | month_from_int 12 = Date.Dec
  | month_from_int _ = raise Match

fun die ls = (
  TextIO.output(TextIO.stdErr,String.concat ls);
  TextIO.output(TextIO.stdErr,"\n");
  OS.Process.exit OS.Process.failure;
  raise (Fail "impossible"))

fun assert b ls = if b then () else die ls

type obj = { hash : string, message : string, date : Date.date }
val empty_obj : obj = { hash = "", message = "", date = Date.fromTimeUniv Time.zeroTime }
fun with_hash x (obj : obj) : obj = { hash = x, message = #message obj, date = #date obj }
fun with_message x (obj : obj) : obj = { hash = #hash obj, message = x, date = #date obj }
fun with_date d (obj : obj) : obj = { hash = #hash obj, message = #message obj, date = d }

type pr = { num : int, head_ref : string, head_obj : obj, base_obj : obj }
val empty_pr : pr = { num = 0, head_ref = "", head_obj = empty_obj, base_obj = empty_obj }
fun with_num x (pr : pr) : pr = { num = x, head_ref = #head_ref pr, head_obj = #head_obj pr, base_obj = #base_obj pr }
fun with_head_ref x (pr : pr) : pr = { num = #num pr, head_ref = x, head_obj = #head_obj pr, base_obj = #base_obj pr }
fun with_head_obj x (pr : pr) : pr = { num = #num pr, head_ref = #head_ref pr, head_obj = x, base_obj = #base_obj pr }
fun with_base_obj x (pr : pr) : pr = { num = #num pr, head_ref = #head_ref pr, head_obj = #head_obj pr, base_obj = x }

datatype integration = Branch of string * obj | PR of pr
type snapshot = { cakeml : integration, hol : obj }

type bare_pr = { head_sha : string, base_sha : string }
datatype bare_integration = Bbr of string | Bpr of bare_pr
type bare_snapshot = { bcml : bare_integration, bhol : string }

fun bare_of_pr ({num,head_ref,head_obj,base_obj}:pr) : bare_pr =
  {head_sha = #hash head_obj, base_sha = #hash base_obj}
fun bare_of_integration (Branch (_,obj)) = Bbr (#hash obj)
  | bare_of_integration (PR pr) = Bpr (bare_of_pr pr)
fun bare_of_snapshot ({cakeml,hol}:snapshot) : bare_snapshot =
  {bcml = bare_of_integration cakeml, bhol = #hash hol}

type line = string
type log_entry = Date.date * line list
type log = log_entry list

type worker_name = string

type job = {
  id : int,
  snapshot : snapshot,
  claimed : (worker_name * Date.date) option,
  output : log
}

local
  val full_date = Date.fmt "%Y %b %d %H:%M:%S"
  val date_len = 4 + 1 + 3 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 2
  fun spaces n = CharVector.tabulate(n,(fn _ => #" "))
in
  fun print_claimed out (worker,date) =
    let
      fun pr s = TextIO.output(out,s)
      val prl = List.app pr
    in
      prl ["Machine: ",worker,"\nClaimed: ",full_date date,"\n"]
    end

  fun print_log_entry out (date,lines) =
    let
      fun pr s = TextIO.output(out,s)
      val prl = List.app pr
      val () = prl[ full_date date, ": "]
    in
      case lines of [] => () | l::ls =>
       (prl [l, "\n"];
        List.app (fn l => prl[spaces (date_len+2), l, "\n"]) ls)
    end

  fun print_snapshot out (s:snapshot) =
    let
      fun pr s = TextIO.output(out,s)
      val prl = List.app pr
      fun print_obj obj =
        prl [#hash obj, "\n  ", #message obj, " (", Date.fmt "%d/%m/%y" (#date obj), ")\n"]

      val () = pr "CakeML: "
      val () =
        case #cakeml s of
          Branch (head_ref,base_obj) => print_obj base_obj
        | PR {num,head_ref,head_obj,base_obj} => (
                 print_obj head_obj;
                 prl ["#", Int.toString num, " (", head_ref, ")\nMerging into: "];
                 print_obj base_obj
               )
      val () = pr "HOL: "
      val () = print_obj (#hol s)
    in () end

  fun print_job out (j:job) =
    let
      val () = print_snapshot out (#snapshot j)
      val () = case #claimed j of NONE => () | SOME claimed => print_claimed out claimed
      val () = List.app (print_log_entry out) (#output j)
    in () end
end

val queue_dirs = ["waiting","active","stopped"]

local
  open OS.FileSys
in
  fun ensure_queue_dirs die =
    let
      val dir = openDir(getDir())
      fun loop ls =
        case readDir dir of NONE => ls
      | SOME d => if isDir d then loop (List.filter(not o equal d) ls)
                  else if List.exists (equal d) ls then die [d," exists and is not a directory"]
                  else loop ls
    in
      List.app mkDir (loop queue_dirs) before closeDir dir
    end
end

local
  open Posix.IO Posix.FileSys
  val flock = FLock.flock {ltype=F_WRLCK, whence=SEEK_SET, start=0, len=0, pid=NONE}
  val smode = S.flags[S.irusr,S.iwusr,S.irgrp,S.iroth]
  val lock_name = "lock"
in
  fun acquire_lock() =
    let
      val fd = Posix.FileSys.creat(lock_name,smode)
      val _ = Posix.IO.setlkw(fd,flock)
    in fd end
end

fun check_id f id =
  0 <= id andalso Int.toString id = f

local
  open OS.FileSys
in
  fun read_list die q () =
    let
      fun die x = die x (* value restriction *)
      val dir = openDir q handle OS.SysErr _ => die ["could not open ",q," directory"]
      fun badFile f = die ["found bad filename ",f," in ",q]
      fun loop acc =
        case readDir dir of NONE => acc
      | SOME f => if isDir (OS.Path.concat(q,f)) handle OS.SysErr _ => die [f, " disappeared from ", q, " unexpectedly"]
                  then die ["found unexpected directory ",f," in ",q]
                  else case Int.fromString f of NONE => badFile f
                       | SOME id => if check_id f id then loop (id::acc) else badFile f
      val ids = loop []
    in ids end
end

fun queue_of_job die f =
  let
    fun mk_path dir = OS.Path.concat(dir,f)
    fun access dir = OS.FileSys.access(mk_path dir, [OS.FileSys.A_READ])
  in
    find access queue_dirs
    handle Match => die ["job ",f," not found"]
  end

fun next_job_id qs =
  1 + List.foldl (fn (q,id) => max id (max_list(q()))) 0 qs

fun read_job_snapshot q id : bare_snapshot =
  let
    val f = OS.Path.concat(q,Int.toString id)
    val inp = TextIO.openIn f handle IO.Io _ => die ["cannot open ",f]
    val invalid = [f," has invalid file format"]
    fun extract_sha prefix line =
      let
        val line = Substring.full line
        val () = assert (Substring.isPrefix prefix line) invalid
      in
        Substring.string(
          Substring.dropr Char.isSpace
            (Substring.triml (String.size prefix) line))
      end
    fun read_line () =
      case TextIO.inputLine inp of
        NONE => die invalid
      | SOME line => line

    val head_sha = extract_sha "CakeML: " (read_line())
    val _ = read_line ()
    val line = read_line ()
    val (line,base_sha) =
      if String.isPrefix "#" line then
        let
          val line = read_line ()
          val _ = read_line ()
        in (read_line(), SOME (extract_sha "Merging into: " line)) end
      else (line, NONE)
    val hol_sha = extract_sha "HOL: " line
    val () = TextIO.closeIn inp
  in
    { bcml = case base_sha
               of NONE => Bbr head_sha
                | SOME base_sha => Bpr { head_sha = head_sha, base_sha = base_sha }
    , bhol = hol_sha }
  end

fun filter_existing snapshots qs =
  let
    exception Return
    fun check_null x = if List.null x then raise Return else x
    fun foldthis q (id,snapshots) =
      check_null
        (List.filter (not o (equal (read_job_snapshot q id)) o bare_of_snapshot) snapshots)
  in
    List.foldl
      (fn ((q,get_ids),snapshots) => List.foldl (foldthis q) snapshots (get_ids()))
    snapshots qs
    handle Return => []
  end

fun remove_if_superseded snapshots id =
  if List.exists (equal (read_job_snapshot "waiting" id) o bare_of_snapshot) snapshots
  then ()
  else OS.FileSys.remove(OS.Path.concat("waiting",Int.toString id))
       handle OS.SysErr _ => die["waiting job ",Int.toString id," disappeared"]

fun file_to_string f =
  let val inp = TextIO.openIn f in TextIO.inputAll inp before TextIO.closeIn inp end

structure Curl = struct
  val token =
    Substring.string (
      Substring.takel (not o Char.isSpace) (
        Substring.full (file_to_string "token")))
  val endpoint = "https://api.github.com/graphql"
  val curl_output_file = "output"
  fun curl_cmd query = String.concat
    ["curl --silent --show-error --output ",curl_output_file,
     " --header 'Authorization: bearer ",token,
     "' --request POST --data '{\"query\" : \"",query,"\"}' ",endpoint]
  fun graphql query =
    let
      val status = OS.Process.system (curl_cmd query) handle OS.SysErr _ => die["failed to execute curl for ",query]
      val () = assert (OS.Process.isSuccess status) ["curl failed for ",query]
    in file_to_string curl_output_file end
end

end
