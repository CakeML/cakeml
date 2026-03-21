structure ml_translatorTrace (* TODO :> ml_translatorTrace *) =
struct

open Feedback boolSyntax Abbrev;

val print_term = Lib.say o Parse.term_to_string
val print_thm = Parse.print_thm
val concl = Thm.concl
val say = Lib.say

   (* ---------------------------------------------------------------------
    * Tracing utilities
    * ---------------------------------------------------------------------*)
    (* TODO add more utilities *)
    datatype action =
             LZ_TEXT of unit -> string
           | TEXT of string;

   val trace_hook : (int * action) Listener.t = Listener.new_listener()
   fun trace x = ignore (Listener.call_listener trace_hook x)

val trace_level = ref 0;
val _ = Feedback.register_trace("ml_translator", trace_level, 7);

fun tty_trace (LZ_TEXT fs) = (say "  "; say (fs ()); say "\n")
  | tty_trace (TEXT s) = (say "  "; say s; say "\n");

(* hol_clock is sometimes a small amount of time in the future under Poly/ML,
   presumably a consequence of being stored in a heap.
*)
fun fudge t = Time.+(t, Time.fromSeconds 10)

val _ = Listener.add_listener trace_hook
        ("default",
         (fn (n,a) => if (n <= !trace_level) then
                        (say "[";
                         say ((Arbnum.toString o #usec o Portable.dest_time o
                               fudge)
                                (#usr (Timer.checkCPUTimer Globals.hol_clock)));
                         say "]: ";
                         tty_trace a)
                      else ()))

end (* struct *)
