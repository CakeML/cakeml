(*
  Implements automatic refreshing of the job queues.
  If there are new jobs on GitHub, they will be added to the waiting queue.
  If there are stale jobs, they will be removed.
*)
use "regressionLib.sml";

open regressionLib

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
  "pullRequests(baseRefName: \\\"master\\\", last: 100, states: [OPEN]){",
  " nodes { mergeable number headRefName",
  " headRef { target { ... on Commit {",
  " oid messageHeadline committedDate }}}",
  "}}}}" ]

val hol_query = String.concat [
  "{repository(name: \\\"HOL\\\", owner: \\\"HOL-Theorem-Prover\\\"){",
  "defaultBranchRef { target { ... on Commit {",
  " oid messageHeadline committedDate }}}}}" ]

fun read1 ss c =
  case Substring.getc ss of SOME (c',ss) =>
    if c = c' then ss
    else die ["expected ",String.str c," got ",String.str c']
  | _ => die ["expected ",String.str c," got nothing"]

fun read_string ss =
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

fun read_dict dispatch acc ss =
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

fun transform reader f acc ss =
  let val (v, ss) = reader ss
  in (f v acc, ss) end

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

val read_obj =
  read_dict
    [("oid", transform read_string with_hash)
    ,("messageHeadline", transform read_string with_message)
    ,("committedDate", transform read_date with_date)
    ] empty_obj

val read_pr =
  read_dict
    [("mergeable", transform read_string mergeable_only)
    ,("number", transform read_number (Option.map o with_num))
    ,("headRefName", transform read_string (Option.map o with_head_ref))
    ,("headRef",
      read_dict
        [("target", transform read_obj (Option.map o with_head_obj))])]
    (SOME empty_pr)

fun get_current_snapshots() : snapshot list =
  let
    val response = GitHub.graphql cakeml_query
    fun add_master obj acc = (Branch("master",obj)::acc)
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
            [("target", transform read_obj add_master)])
          ,("pullRequests",
            read_dict
            [("nodes", transform (read_opt_list read_pr []) add_prs)])
          ])])] []
      (Substring.full response)
    val response = GitHub.graphql hol_query
    fun ignore_acc obj acc = obj
    val (hol_obj,ss) =
      read_dict
      [("data",
        read_dict
        [("repository",
          read_dict
          [("defaultBranchRef",
            read_dict
            [("target", transform read_obj ignore_acc)])])])]
      empty_obj (Substring.full response)
  in
    List.map (fn i => { cakeml = i, hol = hol_obj } )
      cakeml_integrations
  end

val poll_delay = Time.fromSeconds(60 * 10)

fun main() =
  let
    val () = ensure_queue_dirs die
    fun loop() =
      let
        val snapshots = get_current_snapshots()
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
        val () = OS.Process.sleep poll_delay
      in loop () end
  in loop () end
