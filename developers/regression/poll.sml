(*
  Implements automatic refreshing of the job queues.
  If there are new jobs on GitHub, they will be added to the waiting queue.
  If there are stale jobs, they will be removed.
*)
use "regressionLib.sml";

open regressionLib

structure ReadJSON = struct

  type 'a basic_reader = substring -> ('a * substring)
  type 'a reader = 'a -> 'a basic_reader

  fun transform f (reader:'a basic_reader) : 'b reader
  = fn acc => fn ss =>
    let val (v, ss) = reader ss
    in (f v acc, ss) end

  val replace_acc : 'a basic_reader -> 'a reader =
    fn r => transform (fn x => fn _ => x) r

  fun read1 ss c =
    case Substring.getc ss of SOME (c',ss) =>
      if c = c' then ss
      else die ["expected ",String.str c," got ",String.str c']
    | _ => die ["expected ",String.str c," got nothing"]

  val read_string : string basic_reader = fn ss =>
    let
      val ss = read1 ss #"\""
      fun loop ss acc =
        let
          val (chunk,ss) = Substring.splitl (not o equal #"\"") ss
          val z = Substring.size chunk
          val (c,ss) = Substring.splitAt(ss,1)
        in
          if 0 < z andalso Substring.sub(chunk,z-1) = #"\\" then
              loop ss (c::chunk::acc)
          else
            (Option.valOf(String.fromCString(Substring.concat(List.rev(chunk::acc)))),
             ss)
        end
    in
      loop ss []
    end

  fun read_dict (dispatch : (string * 'a reader) list) : 'a reader
  = fn acc => fn ss =>
    let
      val ss = read1 ss #"{"
      fun loop ss acc =
        case Substring.getc ss of
          SOME(#"}",ss) => (acc, ss)
        | SOME(#",",ss) => loop ss acc
        | _ =>
          let
            val (key, ss) = read_string ss
            val ss = read1 ss #":"
            val (acc, ss) = assoc key dispatch acc ss
          in loop ss acc end
    in loop ss acc end

  fun read_opt_list read_item acc ss =
    let
      val ss = read1 ss #"["
      fun loop ss acc =
        case Substring.getc ss of
          SOME(#"]",ss) => (List.rev acc, ss)
        | SOME(#",",ss) => loop ss acc
        | _ =>
          (case read_item ss
           of (NONE, ss) => loop ss acc
            | (SOME v, ss) => loop ss (v::acc))
    in loop ss acc end

  fun mergeable_only "MERGEABLE" acc = acc
    | mergeable_only _ _ = NONE

  val int_from_ss = Option.valOf o Int.fromString o Substring.string

  fun read_date ss =
    let
      val (s, ss) = read_string ss
      val d = Substring.full s
      val (year,d) = Substring.splitl (not o equal #"-") d
      val (month,d) = Substring.splitl (not o equal #"-") (Substring.triml 1 d)
      val (day,d) = Substring.splitl (not o equal #"T") (Substring.triml 1 d)
      val (hour,d) = Substring.splitl (not o equal #":") (Substring.triml 1 d)
      val (minute,d) = Substring.splitl (not o equal #":") (Substring.triml 1 d)
      val (second,d) = Substring.splitl (not o equal #"Z") (Substring.triml 1 d)
      val date = Date.date {
        day = int_from_ss day,
        hour = int_from_ss hour,
        minute = int_from_ss minute,
        month = month_from_int (int_from_ss month),
        offset = SOME (Time.zeroTime),
        second = int_from_ss second,
        year = int_from_ss year }
    in (date, ss) end

  fun read_number ss =
    let val (n,ss) = Substring.splitl Char.isDigit ss
    in (int_from_ss n, ss) end

  val read_obj : obj basic_reader =
    read_dict
      [("oid", transform with_hash read_string)
      ,("messageHeadline", transform with_message read_string)
      ,("committedDate", transform with_date read_date)
      ] empty_obj

  val read_pr : pr option basic_reader =
    read_dict
      [("mergeable", transform mergeable_only read_string)
      ,("number", transform (Option.map o with_num) read_number)
      ,("headRefName", transform (Option.map o with_head_ref) read_string)
      ,("headRef",
        read_dict
          [("target", transform (Option.map o with_head_obj) read_obj)])]
      (SOME empty_pr)

end

val waiting = read_list die "waiting"
val active  = read_list die "active"
val stopped = read_list die "stopped"

fun add_waiting (snapshot,id) =
  let
    val f = Int.toString id
    val path = OS.Path.concat("waiting",f)
    val () = assert (not(OS.FileSys.access(path, []))) ["job ",f," already exists waiting"]
    val out = TextIO.openOut path
    val () = print_snapshot out snapshot
    val () = TextIO.closeOut out
  in id+1 end

val cakeml_query = String.concat [
  "{repository(name: \\\"cakeml\\\", owner: \\\"CakeML\\\"){",
  "defaultBranchRef { target { ... on Commit {",
  " oid messageHeadline committedDate }}}",
  "pullRequests(baseRefName: \\\"master\\\", first: 100, states: [OPEN]",
  " orderBy: {field: CREATED_AT, direction: DESC}){",
  " nodes { mergeable number headRefName",
  " headRef { target { ... on Commit {",
  " oid messageHeadline committedDate }}}",
  "}}}}" ]

val hol_query = String.concat [
  "{repository(name: \\\"HOL\\\", owner: \\\"HOL-Theorem-Prover\\\"){",
  "defaultBranchRef { target { ... on Commit {",
  " oid messageHeadline committedDate }}}}}" ]

local
  open ReadJSON
in
  fun get_current_snapshots () : snapshot list =
    let
      val response = GitHub.graphql cakeml_query
      fun add_master obj acc = (Branch("master",obj)::acc)
      (* This assumes the PR base always matches master.
         We could read it from GitHub instead. *)
      fun add_prs prs [m as (Branch(_,base_obj))] =
        m :: (List.map (PR o with_base_obj base_obj) prs)
      | add_prs _ _ = die ["add_prs"]
      val (cakeml_integrations,ss) =
        read_dict
        [("data",
          read_dict
          [("repository",
            read_dict
            [("defaultBranchRef",
              read_dict
              [("target", transform add_master read_obj)])
            ,("pullRequests",
              read_dict
              [("nodes", transform add_prs (read_opt_list read_pr []))])
            ])])] []
        (Substring.full response)
      val response = GitHub.graphql hol_query
      val (hol_obj,ss) =
        read_dict
        [("data",
          read_dict
          [("repository",
            read_dict
            [("defaultBranchRef",
              read_dict
              [("target", replace_acc read_obj)])])])]
        empty_obj (Substring.full response)
    in
      List.map (fn i => { cakeml = i, hol = hol_obj } )
        (List.rev cakeml_integrations) (* after rev: oldest pull request first, master last *)
    end
end

fun main () =
  let
    val no_poll = List.exists (equal"--no-poll") (CommandLine.arguments())
    val () = ensure_queue_dirs die
    fun loop () =
      let
        val snapshots = get_current_snapshots ()
        val fd = acquire_lock ()
        val () = List.app (remove_if_superseded snapshots) (waiting())
        val to_queue =
          filter_existing snapshots
            [("waiting",waiting),
             ("active" ,active ),
             ("stopped",stopped)]
        val () = if List.null to_queue then ()
                 else ignore (List.foldl add_waiting (next_job_id [waiting,active,stopped]) to_queue)
        (* TODO: stop timed out jobs *)
        val () = Posix.IO.close fd
      in
        if no_poll then ()
        else (OS.Process.sleep poll_delay; loop ())
      end
  in loop () end
