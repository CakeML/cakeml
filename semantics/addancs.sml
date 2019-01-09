(*
  A script to add a set_grammar_ancestry line to a generated Script.sml file.
*)
fun warn s =
  (TextIO.output(TextIO.stdErr, s ^ "\n"); TextIO.flushOut TextIO.stdErr)

fun die s =
  (warn s; OS.Process.exit OS.Process.failure)

fun includes_ancestry fname =
  let
    val istrm = TextIO.openIn fname
    fun recurse () =
      case TextIO.inputLine istrm of
          NONE => false
        | SOME s =>
            String.isSubstring "set_grammar_ancestry" s orelse recurse()
  in
    recurse () before TextIO.closeIn istrm
  end

fun insert_ancestors fname ancs =
  let
    val istrm = TextIO.openIn fname
    val ancline = "val _ = set_grammar_ancestry [" ^
                  String.concatWith
                    ", "
                    (map (fn s => "\"" ^ String.toString s ^ "\"") ancs) ^
                  "];\n"
    val openline = "local open " ^
                  String.concatWith
                    " "
                    (map (fn s => String.toString s ^ "Theory") ancs) ^
                  " in end;\n"
    fun readInsert lnum seen_ntp acc =
      case TextIO.inputLine istrm of
          NONE => if seen_ntp then List.rev acc
                  else die "Didn't see a new_theory line"
        | SOME s =>
          if String.isSubstring "val _ = new_theory" s then
            if seen_ntp then
              die (fname^":"^Int.toString lnum^": Seen second new_theory line")
            else
              readInsert (lnum + 1) true (ancline :: s :: openline :: acc)
          else readInsert (lnum + 1) seen_ntp (s::acc)
    val lines = readInsert 1 false []
    val _ = TextIO.closeIn istrm
    val outstrm = TextIO.openOut fname
  in
    List.app (fn s => TextIO.output(outstrm, s)) lines;
    TextIO.closeOut outstrm
  end

fun main() =
  let
    val args = CommandLine.arguments()
    val usage_str = "Usage:\n  " ^ CommandLine.name() ^ " fname anc1 .. ancn\n"
  in
    case args of
        [] => die usage_str
      | ["-h"] => TextIO.output(TextIO.stdOut, usage_str)
      | [_] => die usage_str
      | fname::ancs => insert_ancestors fname ancs
  end
