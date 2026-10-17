(*
  rawBridge program example: forward Ethernet frames between two interfaces.
*)
Theory rawBridgeProg
Ancestors
  misc
Libs
  preamble basis

val _ = translation_extends "basisProg";

Quote add_cakeml:
  fun forward src dst index =
    case SocketIO.rawRecv src 65535 of
      None => ()
    | Some frame => SocketIO.rawSendTo dst index frame

  fun bridge s0 i0 s1 i1 =
    ((case SocketIO.poll [(s0, SocketIO.pollIn), (s1, SocketIO.pollIn)] (~1) of
        Some [e0, e1] =>
          (if e0 <> 0 then forward s0 s1 i1 else ();
           if e1 <> 0 then forward s1 s0 i0 else ())
      | _ => ());
     bridge s0 i0 s1 i1)

  (* bridges the two interfaces named on the command line until killed;
     raw sockets need CAP_NET_RAW, so run as root or in a user namespace *)
  fun rawBridge u =
    case CommandLine.arguments () of
      [if0, if1] =>
        (let val s0 = SocketIO.rawSocket ()
             val s1 = SocketIO.rawSocket ()
             val i0 = SocketIO.ifIndex s0 if0
             val i1 = SocketIO.ifIndex s1 if1
         in
           SocketIO.rawBind s0 i0;
           SocketIO.rawBind s1 i1;
           bridge s0 i0 s1 i1
         end
         handle SocketIO.SocketError =>
           TextIO.print_err "rawBridge: socket error (is CAP_NET_RAW granted?)\n")
    | _ => TextIO.print_err "usage: rawBridge <interface> <interface>\n"
End

Quote main = cakeml:
  rawBridge ();
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

Definition rawBridge_prog_def:
  rawBridge_prog = ^prog
End
