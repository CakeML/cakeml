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
    val output = system_output (git_path,["rev-parse","--verify","HEAD"])
    val () =
      if String.isPrefix sha output then () else
      (system_output (git_reset sha);
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
      (configured andalso
       (system_capture "bin/build --nograph"
        orelse on_failure ()))
      orelse on_failure ()
      before OS.FileSys.chDir OS.Path.parentArc
    end
end

local
  val time_options = String.concat["--format='%E %Kk' --output='",timing_file,"'"]
in
  fun run_regression id =
    let
      val root = OS.FileSys.getDir()
      val holdir = OS.Path.concat(root,HOLDIR)
      val holmake_cmd =
        String.concat["HOLDIR='",holdir,"' /usr/bin/time ",time_options,
                      " '",holdir,"/bin/Holmake' --qof"]
      val cakemldir = OS.Path.concat(root,CAKEMLDIR)
      val () = OS.FileSys.chDir CAKEMLDIR
      (* val () = assert (OS.FileSys.getDir() = cakemldir) ["impossible"] *)
      val seq = TextIO.openIn("developers/build-sequence")
      fun loop () =
        case TextIO.inputLine seq of NONE => true
        | SOME line =>
          if String.isPrefix "#" line orelse
             String.isPrefix "\n" line
          then loop () else
          let
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
                 loop ())
              else on_failure ()
            else on_failure ()
          end
    in
      if loop () then
        let
          val () = API.append id "SUCCESS"
          val () = API.stop id
        in true end
      else false
    end
end

fun work id =
  let
    val response = API.send (Job id)
  in
    if String.isPrefix "Error:" response
    then warn [response] else
    let
      val invalid = ["job ",Int.toString id," returned invalid response"]
      val {bcml,bhol} = read_bare_snapshot invalid (TextIO.openString response)
      val () = prepare_hol bhol
      val () = prepare_cakeml bcml
    in
      ignore (build_hol id andalso run_regression id)
    end
  end

fun main () =
  let
    val no_poll = List.exists (equal"--no-poll") (CommandLine.arguments())
    val name = file_to_line "name"
    fun loop () =
      let
        val waiting_ids =
          List.map (Option.valOf o Int.fromString)
            (String.tokens Char.isSpace (API.send Waiting))
      in
        case waiting_ids of [] =>
          if no_poll then ()
          else (OS.Process.sleep poll_delay; loop ())
        | (id::_) => (* could prioritise for ids that match our HOL dir *)
          let
            val response = API.send (Claim(id,name))
            val () = if response=claim_response
                     then work id
                     else warn ["Claim failed: ",response]
          in loop () end
      end
  in loop () end
