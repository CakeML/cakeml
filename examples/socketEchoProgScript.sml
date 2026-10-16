(*
  socketEcho program example: echo a client's data over a Unix domain socket.
*)
Theory socketEchoProg
Ancestors
  misc
Libs
  preamble basis

val _ = translation_extends "basisProg";

Quote add_cakeml:
  fun echoLoop conn =
    let val s = SocketIO.recv conn 4096 in
      if s = "" then ()
      else (SocketIO.send conn s; echoLoop conn)
    end

  (* waits up to ten seconds for a client on the socket path given on the
     command line, then echoes until the client closes the connection *)
  fun socketEcho u =
    case CommandLine.arguments () of
      [path] =>
        (let val listener = SocketIO.listen path in
           (case SocketIO.poll [(listener, SocketIO.pollIn)] 10000 of
              None => TextIO.print_err "socketEcho: no client within ten seconds\n"
            | Some _ =>
                let val conn = SocketIO.accept listener in
                  (echoLoop conn; SocketIO.close conn)
                end);
           SocketIO.close listener
         end
         handle SocketIO.SocketError => TextIO.print_err "socketEcho: socket error\n")
    | _ => TextIO.print_err "usage: socketEcho <socket path>\n"
End

Quote main = cakeml:
  socketEcho ();
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition socketEcho_prog_def:
  socketEcho_prog = ^prog
End
