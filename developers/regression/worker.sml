(*
  Worker that claims and runs regression test jobs.

  Assumes the following are available:
    /usr/bin/curl, /usr/bin/git, /usr/bin/time, poly

  Also assumes the default shell (/bin/sh) understands
    ENV=val ... cmd [args ...] &>file
  to mean redirect both stdout and stderr to file when running
  cmd on args in an environment augmented by the (ENV,val) pairs.

  Can be run either as a daemon (default) that will keep looking for work by
  polling or as a one-shot command (--no-poll) that will do nothing if no work
  is currently available. This means polling or work notifications can be
  handled externally if desired.

  Summary of options:
    --no-poll   : Exit when no waiting jobs are found rather than polling.
                  Will still check for more waiting jobs after completing a job.
    --no-loop   : Exit after finishing a job, do not check for more waiting jobs.
    --select id : Ignore the waiting jobs list and instead attempt to claim job <id>.
    --resume id : Assume job <id> has previously been claimed by this worker and
                  attempt to start running it again.

  All work will be carried out in the current directory
  (or subdirectories of it) with no special permissions.
  Assumes this directory starts empty except for the
  worker executable and one file
    name
  containing this worker node's identity. This could be
  created as follows:
    uname -norm > name
  It must not start with whitespace nor contain any single quotes.

  Manipulates working directories for HOL and CakeML, which are created if
  necessary. If a job can reuse the HOL working directory without rebuilding
  (the commit has not changed), then it will be reused. Otherwise, it is
  cleaned ("git clean -xdf") and rebuilt. The CakeML working directory is
  cleaned before every job.

  Jobs are handled as follows:
    1. Find a job in the waiting queue
    2. Claim the job
    3. Set up HOL and CakeML working directories
       according to the job snapshot
    4. Build HOL, capturing stdout and stderr
       On failure:
         1. Append "FAILED: building HOL"
         2. Log the captured output
         3. Stop the job
    5. For each directory in the CakeML build sequence
       1. Append "Starting to build <dir>"
       2. Holmake in that directory,
            capturing stdout and stderr,
            and capturing time and memory usage
          On failure:
            1. Append "FAILED: building <dir>"
            2. Log the captured output
            3. Stop the job
       3. Append "Finished <dir>: <time> <memory>"
    6. Append "SUCCESS"
    7. Stop the job
*)

use "regressionLib.sml";

open regressionLib

val HOLDIR = "HOL"
val hol_remote = "https://github.com/HOL-Theorem-Prover/HOL.git"
val CAKEMLDIR = "cakeml"
val cakeml_remote = "https://github.com/CakeML/cakeml.git"
val git_path = "/usr/bin/git"
val git_clean = (git_path,["clean","-d","--force","-x"])
fun git_reset sha = (git_path,["reset","--hard","--quiet",sha])
val git_fetch = (git_path,["fetch","origin"])
fun git_sha_of head = (git_path,["rev-parse","--verify",head])
val git_head = git_sha_of "HEAD"
val git_merge_head = git_sha_of "MERGE_HEAD"

local
  open OS.FileSys
in
  fun ensure_clone_exists remote options dir =
    if access (dir,[]) then
      if isDir dir then
        let
          val () = chDir dir
          val output = system_output (git_path,["remote","get-url","origin"])
          val () = chDir OS.Path.parentArc
        in
          assert (String.isPrefix remote output) [dir," remote misconfigured"]
        end
      else die [dir," is not a directory"]
    else
      let
        val () = diag [dir," does not exist: will clone"]
        val status = OS.Process.system (String.concat[git_path," clone ",options,remote," ",dir])
      in
        assert (OS.Process.isSuccess status) ["git clone failed for ",dir]
      end
end

fun ensure_hol_exists () = ensure_clone_exists hol_remote "--single-branch " HOLDIR
fun ensure_cakeml_exists () = ensure_clone_exists cakeml_remote "" CAKEMLDIR

fun prepare_hol sha =
  let
    val () = ensure_hol_exists ()
    val () = OS.FileSys.chDir HOLDIR
    val output = system_output git_fetch
    val output = system_output git_head
    val () =
      if String.isPrefix sha output
      then diag ["re-using HOL working directory at same commit"]
      else (system_output (git_reset sha);
            ignore (system_output git_clean))
  in
    OS.FileSys.chDir OS.Path.parentArc
  end

fun prepare_cakeml x =
  let
    val () = ensure_cakeml_exists ()
    val () = OS.FileSys.chDir CAKEMLDIR
    val output = system_output git_fetch
    val _ =
      case x of
        Bbr sha => system_output (git_reset sha)
      | Bpr {head_sha, base_sha} =>
          (system_output (git_reset base_sha);
           system_output (git_path,["merge","--no-commit","--quiet",head_sha]))
    val _ = system_output git_clean
  in
    OS.FileSys.chDir OS.Path.parentArc
  end

local
  val configure_hol = "poly --script tools/smart-configure.sml"
in
  fun build_hol id =
    let
      fun on_failure () =
        let
          val () = API.append id "FAILED: building HOL"
          val () = API.log id capture_file
          val () = API.stop id
        in false end
      val () = OS.FileSys.chDir HOLDIR
      val configured =
        OS.FileSys.access("bin/build",[OS.FileSys.A_EXEC])
        orelse system_capture configure_hol
    in
      ((configured andalso
        (system_capture "bin/build --nograph"
         orelse on_failure ()))
       orelse on_failure ())
      before OS.FileSys.chDir OS.Path.parentArc
    end
end

local
  val resume_file = "resume"
  val time_options = String.concat["--format='%E %Kk' --output='",timing_file,"'"]
  fun no_skip _ = false
in
  fun run_regression resumed id =
    let
      val root = OS.FileSys.getDir()
      val holdir = OS.Path.concat(root,HOLDIR)
      val holmake_cmd =
        String.concat["HOLDIR='",holdir,"' /usr/bin/time ",time_options,
                      " '",holdir,"/bin/Holmake' --qof"]
      val cakemldir = OS.Path.concat(root,CAKEMLDIR)
      val () = OS.FileSys.chDir CAKEMLDIR
               handle e as OS.SysErr _ => die ["failed to enter ",CAKEMLDIR,
                                               "\n","root: ",root,
                                               "\n",exnMessage e]
      val () = assert (OS.FileSys.getDir() = cakemldir) ["impossible failure"]
      val seq = TextIO.openIn("developers/build-sequence")
                handle e as OS.SysErr _ => die ["failed to open build-sequence: ",exnMessage e]
      val can_skip =
        if resumed then (not o equal (file_to_string resume_file)) else no_skip
        handle (e as IO.Io _) => die["failed to load resume file: ",exnMessage e]
      fun loop can_skip =
        case TextIO.inputLine seq of NONE => true
        | SOME line =>
          if String.isPrefix "#" line orelse
             String.isPrefix "\n" line orelse
             can_skip line
          then loop can_skip else
          let
            val resume_out = TextIO.openOut resume_file
            val () = TextIO.output(resume_out,line)
            and () = TextIO.closeOut resume_out
            val dir = until_space line
            val () = API.append id (String.concat["Starting to build ",dir])
            fun on_failure () =
              let
                val () = API.append id (String.concat["FAILED: building ",dir])
                val () = API.log id capture_file
                val () = API.stop id
              in false end
            val entered = (OS.FileSys.chDir dir; true)
                          handle e as OS.SysErr _ => (API.append id (exnMessage e); false)
          in
            if entered then
              if system_capture holmake_cmd then
                (API.append id (String.concat["Finished ",dir,": ",file_to_line timing_file]);
                 OS.FileSys.chDir cakemldir;
                 loop no_skip)
              else on_failure ()
            else on_failure ()
          end
      val success = loop can_skip
      val () =
        if success then
          (API.append id "SUCCESS"; API.stop id)
        else ()
      val () = OS.FileSys.chDir root
    in
      success
    end
end

fun validate_resume jid bhol bcml =
  let
    val () = diag ["checking HOL for resuming job ",jid]
    val () = OS.FileSys.chDir HOLDIR
    val head = system_output git_head
    val () = assert (head = bhol) ["wrong HOL commit"]
    val () = OS.FileSys.chDir OS.Path.parentArc
    val () = diag ["checking CakeML for resuming job ",jid]
    val () = OS.FileSys.chDir CAKEMLDIR
    val () =
      case bcml of
        Bbr sha => assert (system_output git_head = sha) ["wrong CakeML commit"]
      | Bpr {head_sha, base_sha} =>
        (assert (system_output git_head = base_sha) ["wrong CakeML base commit"];
         assert (system_output git_merge_head = head_sha) ["wrong CakeML head commit"])
    val () = OS.FileSys.chDir OS.Path.parentArc
  in
    true
  end

fun work resumed id =
  let
    val response = API.send (Job id)
    val jid = Int.toString id
  in
    if String.isPrefix "Error:" response
    then (warn [response]; false) else
    let
      val invalid = ["job ",jid," returned invalid response"]
      val {bcml,bhol} = read_bare_snapshot invalid (TextIO.openString response)
      val built_hol =
        if resumed then validate_resume jid bhol bcml
        else let
          val () = diag ["preparing HOL for job ",jid]
          val () = prepare_hol bhol
          val () = diag ["preparing CakeML for job ",jid]
          val () = prepare_cakeml bcml
          val () = diag ["building HOL for job ",jid]
        in
          build_hol id
        end
    in
      built_hol andalso
      (diag ["running regression for job ",jid];
       run_regression resumed id)
    end
  end

fun get_int_arg name [] = NONE
  | get_int_arg name [_] = NONE
  | get_int_arg name (x::y::xs) =
    if x = name then Int.fromString y
    else get_int_arg name (y::xs)

fun main () =
  let
    val args = CommandLine.arguments()
    val no_poll = List.exists (equal"--no-poll") args
    val no_loop = List.exists (equal"--no-loop") args
    val resume = get_int_arg "--resume" args
    val select = get_int_arg "--select" args
    val name = file_to_line "name"
               handle IO.Io _ => die["Could not determine worker name. Try uname -norm >name."]
    fun loop resume =
      let
        val waiting_ids =
          case select of SOME id => [id] | NONE =>
          case resume of SOME id => [id] | NONE =>
          List.map (Option.valOf o Int.fromString)
            (String.tokens Char.isSpace (API.send Waiting))
      in
        case waiting_ids of [] =>
          if no_poll then ()
          else (OS.Process.sleep poll_delay; loop NONE)
        | (id::_) => (* could prioritise for ids that match our HOL dir *)
          let
            val resumed = Option.isSome resume
            val response = if resumed
                           then claim_response
                           else API.send (Claim(id,name))
            val success =
              if response=claim_response
              then work resumed id
              else (warn ["Claim of job ",Int.toString id," failed: ",response]; false)
          in
            if no_loop orelse (resumed andalso not success)
            then ()
            else loop NONE
          end
      end handle e => die ["unexpected failure: ",exnMessage e]
  in loop resume end
