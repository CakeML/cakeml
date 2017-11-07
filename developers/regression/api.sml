(*
  Implements the server-side regression-test API as a CGI program.
  The API is for workers to view and manipulate the job queues.
*)
use "regressionLib.sml";

open regressionLib

val text_response_header = "Content-Type:text/plain\n\n"

fun text_response s =
  let
    val () = TextIO.output(TextIO.stdOut, text_response_header)
    val () = TextIO.output(TextIO.stdOut, s)
    val () = TextIO.output(TextIO.stdOut, "\n")
  in () end

fun cgi_die ls =
  (List.app (fn s => TextIO.output(TextIO.stdOut, s))
     (text_response_header::"Error:\n"::ls);
   TextIO.output(TextIO.stdOut,"\n");
   OS.Process.exit OS.Process.success;
   raise (Fail "impossible"))

fun cgi_assert b ls = if b then () else cgi_die ls

val waiting = read_list cgi_die "waiting"
val active  = read_list cgi_die "active"
val stopped = read_list cgi_die "stopped"

fun job id =
  let
    val f = Int.toString id
    val q = queue_of_job cgi_die f
  in
    OS.Path.concat(q,f)
  end

fun claim id name =
  let
    val f = Int.toString id
    val old = OS.Path.concat("waiting",f)
    val new = OS.Path.concat("active",f)
    val () =
      if OS.FileSys.access(old,[OS.FileSys.A_READ]) then
        if OS.FileSys.access(new,[OS.FileSys.A_READ]) then
          cgi_die ["job ",f, " is both waiting and active"]
        else OS.FileSys.rename{old = old, new = new}
      else cgi_die ["job ",f," is not waiting to be claimed"]
    val out = TextIO.openAppend new
  in
    print_claimed out (name,Date.fromTimeUniv(Time.now())) before TextIO.closeOut out
  end

fun append id data =
  let
    val f = Int.toString id
    val p = OS.Path.concat("active",f)
    val out = TextIO.openAppend p handle e as IO.Io _ => (cgi_die ["job ",f," is not active: cannot append"]; raise e)
  in
    print_log_entry out (Date.fromTimeUniv(Time.now()),data) before TextIO.closeOut out
  end

fun stop id =
  let
    val f = Int.toString id
    val old = OS.Path.concat("active",f)
    val new = OS.Path.concat("stopped",f)
    val () =
      if OS.FileSys.access(old,[OS.FileSys.A_READ]) then
        if OS.FileSys.access(new,[OS.FileSys.A_READ]) then
          cgi_die ["job ",f, " is both active and stopped"]
        else OS.FileSys.rename{old = old, new = new}
      else cgi_die ["job ",f," is not active: cannot stop"]
  in
    () (* TODO: send email *)
  end

fun retry id =
  let
    val f = Int.toString id
    val old = OS.Path.concat("stopped",f)
    val () = cgi_assert (OS.FileSys.access(old,[OS.FileSys.A_READ])) ["job ",f," is not stopped: cannot retry"]
    val id = next_job_id [waiting,active,stopped]
    val new = OS.Path.concat("waiting",Int.toString id)
    val inp = TextIO.openIn old
    val out = TextIO.openOut new
    fun loop last =
      case TextIO.inputLine inp of NONE => cgi_die ["stopped job ",f," has invalid file format"]
      | SOME line => (TextIO.output(out,line);
                      if last then () else
                      loop (String.isPrefix "HOL: " line))
    val () = loop false
    val () = TextIO.closeOut out
    val () = TextIO.closeIn inp
  in id end

type id = int

datatype api = Waiting | Active | Stopped
             | Job of id | Claim of id * worker_name
             | Append of id * line list
             | Stop of id | Retry of id

local
  fun get_id n =
    case Int.fromString n of NONE => NONE
    | SOME id => if check_id n id then SOME id else NONE
  fun guard b x = if b then SOME x else NONE
  fun mguard b f x = if b then Option.map f x else NONE
  fun mguard2 b f x y = if b then Option.join (Option.map (fn x => Option.map (fn y => f(x,y)) y) x) else NONE
in
  fun get_api() =
    case (OS.Process.getEnv "PATH_INFO",
          OS.Process.getEnv "REQUEST_METHOD") of
      (SOME path_info, SOME request_method) =>
      if path_info = "/waiting" then guard (request_method="GET") Waiting
      else if path_info = "/active" then guard (request_method="GET") Active
      else if path_info = "/stopped" then guard (request_method="GET") Stopped
      else (case String.tokens (equal #"/") path_info of
        ["job",n] => mguard (request_method="GET") Job (get_id n)
      | ["claim",n,s] => mguard (request_method="GET") (fn id => Claim(id,s)) (get_id n)
      | ["append",n] => mguard2 (request_method="POST") Append
          (get_id n)
          (Option.map
            (fn len => String.fields (equal #"\n") (TextIO.inputN(TextIO.stdIn,len)))
            (Option.composePartial(Int.fromString,OS.Process.getEnv) "CONTENT_LENGTH"))
      | ["stop",n] => mguard (request_method="GET") Stop (get_id n)
      | ["retry",n] => mguard (request_method="GET") Retry (get_id n)
      | _ => NONE)
    | _ => NONE
end

local
  fun id_list ids = String.concatWith ", " (List.map Int.toString ids)
in
  fun dispatch api =
    text_response (
      case api of
        Waiting => id_list (waiting())
      | Active => id_list (active())
      | Stopped => id_list (stopped())
      | Job id => let val inp = TextIO.openIn(job id) in TextIO.inputAll inp before TextIO.closeIn inp end
      | Claim(id,name) => (claim id name; "claimed")
      | Append(id,data) => (append id data; "appended")
      | Stop id => (stop id; "stopped")
      | Retry id => String.concat["retried as job ",Int.toString(retry id)]
    ) handle e => cgi_die [exnMessage e]
end

fun main() =
  let
    val () = ensure_queue_dirs cgi_die
    val () = case get_api() of NONE => cgi_die ["bad usage"]
             | SOME api =>
               let val fd = acquire_lock()
               in dispatch api before Posix.IO.close fd end
  in
    OS.Process.exit OS.Process.success
  end
