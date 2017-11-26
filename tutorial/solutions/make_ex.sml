(*
   This SML program generates makes a copy of its argument files in the parent
   folder where the "(*ex *) ... (* ex*)" blocks have been removed
*)

exception NotAFile of string;

fun copy_until_solution_start src dst =
  case TextIO.inputLine src of
       NONE =>  ()
     | SOME line => if String.isSubstring "(*ex" line
                    then drop_until_solution_end src dst
                    else (TextIO.output(dst, line);
                          copy_until_solution_start src dst)

and drop_until_solution_end src dst =
  case TextIO.inputLine src of
       NONE => ()
     | SOME line => if String.isSubstring "ex*)" line
                    then copy_until_solution_start src dst
                    else drop_until_solution_end src dst;

fun handle_file fname =
  let val src = TextIO.openIn(fname)
      (* In CakeML, BadFilename should take the filename as string *)
      val dst = TextIO.openOut("../" ^ fname)
      (* CakeMl's openOut is probably not correct on unexisting files *)
      val _ = copy_until_solution_start src dst
      val _ = TextIO.closeIn(src)
      val _ = TextIO.closeOut(dst)
  in () end;

val main = List.app handle_file o CommandLine.arguments
