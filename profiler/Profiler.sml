(*
   Basic profiling facilities for theories and proofs to generate flame graphs (and flame charts) using FlameGraph.
*)
structure Profiler =
struct

(* The average user is probably mainly interested in `profile_tac`,
 * `profile` and `export`, which have examples in their documentation. *)

(* Various helpers *)
infix |>
fun x |> f = f x

(* Marks the start and stop times of a profiler call. *)
datatype event = START | STOP
fun event_to_string START = "START"
  | event_to_string STOP = "STOP"

(* Type for a (raw) data point. *)
type row = string * event * Time.time
fun row_to_string (n, e, t) =
    String.concat [
      "(",
      String.concatWith ", " [n, event_to_string e, Time.toString t],
      ")"
    ]
(* Type for a data point with the entire stack. *)
type stacked_row = string list * event * Time.time
fun stack_to_string stack = String.concatWith ";" stack
fun stacked_row_to_string (ns, e, t) =
    String.concat [
      "(",
      String.concatWith ", " [
        stack_to_string ns, event_to_string e, Time.toString t
      ],
      ")"
    ]

(* The idea is that the profiler simply prepends new entries, which
 * hopefully reduces the amount of overhead. *)
val data = ref ([] : row list)
fun reset_data () = data := []

(* Creates a profiling version of a tactic.
 *
 * This function can be used to create profiling versions of tactics, for example:
 * `fun gvs thms = profile_tac "gvs" (bossLib.gvs thms)`
 * `val CASE_TAC = profile_tac "CASE_TAC" BasicProvers.CASE_TAC`
 * Note how we use the fully qualified name on the right-hand side. Without it,
 * `gvs` would be defined as a function that immediately calls itself, whereas
 * sending the definition of `CASE_TAC` n times would lead to `CASE_TAC` adding
 * n data points every time it is used. *)
fun profile_tac name tac g = let
  val _ = data := (name, START, Time.now())::(!data)
  (* Without this handler, we might generated events that never terminate, which
   * we assume does not happen during data processing. *)
  val r = tac g handle e => (data := (name, STOP, Time.now())::(!data); raise e)
  val _ = data := (name, STOP, Time.now())::(!data)
in r end

(* Profiles evaluation of an expression.

 * Suppose we have the following piece of code:
 * `val r = (g 7) + 3`
 * and we suspect that evaluating `g 7` takes a long time. To quantify this,
 * we can use:
 * `val r = (profile "g_7" (fn () => g 7)) + 3` *)
fun profile (name: string) (f: unit -> 'a) : 'a = let
  val _ = data := (name, START, Time.now())::(!data)
  val r = f () handle e => (data := (name, STOP, Time.now())::(!data); raise e)
  val _ = data := (name, STOP, Time.now())::(!data)
in r end

(* Returns the input data with time relative to the first row.
 * Assumes data is stored newest to oldest. *)
fun normalize (data: row list) : row list =
    case data of
        [] => []
      | data => let
        val start = #3 (List.last data)
      in map (fn (n,e,t) => (n,e,t-start)) data end

(* Returns the input data with the names updated to contain the full stack.
 * Assumes data is stored newest and returns the data in reversed order
 * (oldest to newest). *)
fun build_stack (data: row list) : (stacked_row list) = let
  fun aux [] [] acc = acc
    | aux [] _ _ = raise Fail "build_stack: out of data"
    | aux ((name, STOP, time)::data') stops acc =
      aux data' (name::stops) ((rev (name::stops), STOP, time)::acc)
    | aux (_::_) [] _ = raise Fail "build_stack: out of stops"
    | aux ((r as (name, START, time))::data') (stops as (name'::stops')) acc =
      if name' <> name
      then raise Fail (String.concatWith " " [
                          "build_stack: name mismatch between ",
                          row_to_string r,
                          "and",
                          name])
      else aux data' stops' ((rev stops, START, time)::acc)
in aux data [] [] end

(* Returns data with consecutive starts and stops broken up with stop and start
 * respectively.
 * Assumes data is given from oldest to newest.
 *
 * For example, a sequence START START START STOP STOP STOP is turned into
 * START STOP START STOP START STOP START STOP START STOP with the names and
 * clocks set accordingly. *)
fun make_intervals (data: stacked_row list) : stacked_row list =
    (* Writing this was much painful than it should have been :( *)
    case data of
        [] => []
      | [(_, START, _)] => raise Fail "make_intervals: unmatched START"
      | [(_, STOP, _)] => data
      | (r1 as (names1,event1,time1))::(r2 as (names2,event2,time2))::rest =>
        (case (event1,event2) of
             (START, START) => r1::(make_intervals ((names1,STOP,time2)::r2::rest))
           | (START, STOP) =>
             if names1 <> names2
             then raise Fail (String.concatWith " " [
                                 "make_intervals: name mismatch between ",
                                 stacked_row_to_string r1,
                                 "and",
                                 stacked_row_to_string r2])
             else r1::make_intervals (r2::rest)
           | (STOP, START) => r1::(make_intervals (r2::rest))
           | (STOP, STOP) => r1::(make_intervals ((names2,START,time1)::r2::rest)))

(* Collapses intervals into their duration.
 * Assumes data is stored oldest to newest. *)
fun collapse (data: stacked_row list) =
    case data of
        [] => []
      | (names,START,time)::(names',STOP,time')::data' =>
        if names <> names' then raise Fail "name mismatch"
        else if time' < time then raise Fail "clock non-monotonic"
        else (names, time' - time)::(collapse data')
      | _ => raise Fail "bad intervals"

(* Writes the data to path in a format that can be used by FlameGraph.
 *
 * The data can be used by https://github.com/brendangregg/FlameGraph
 * to generate flame graphs and flame charts.
 * The relevant command is `./flamegraph.pl --flamechart ~/in.txt > ~/out.svg`
 * with the paths adjusted accordingly. *)
fun export (path: string) : unit = let
  val out = TextIO.openOut path
  (* Brief research indicates that the clock maybe has a resolution of 10ms, which is
   * why we export miliseconds. *)
  fun time_to_string time = LargeInt.toString (Time.toMilliseconds time)
  fun print_element (stack, time) = String.concat [stack_to_string stack, " ", time_to_string time, "\n"]
  fun write_element e = TextIO.output (out, print_element e)
  val elements = !data |> normalize |> build_stack |> make_intervals |> collapse
                       (* |> insert_start |> insert_stop |> collapse *)
in
  app write_element elements;
  TextIO.closeOut out
end

(* Writes to the file ‘name’ in the current working directory - wherever that may be.
 *
 * One use of this could be for example at the end of theories:
 * ‘val _ = Profiler.export_cwd "HashtableProof.txt";’ *)
fun export_cwd (name: string) =
    export (OS.Path.concat (OS.FileSys.getDir(), "HashtableProof.txt"))
end
