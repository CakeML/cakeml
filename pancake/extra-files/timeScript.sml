(*
  Attempt to formalise timing constructs and functions of Ada.Real_Time
  (more of documentation)
*)

open preamble
     mlstringTheory

val _ = new_theory "time";

(* Ada.Real_Time has three types: time, time_span, second_conut *)


(* from Add manual: The set of values of type Time corresponds one-to-one with an implementation-defined
   range of mathematical integers,
   so should we name time as int?  *)

Type time = ``:num``

(*
  Values of the type Time_Span represent length of real time duration.
  The set of values of this type corresponds one-to-one with an implementation-defined
  range of mathematical integers. *)

Type time_span = ``:num``


(*
  A value of type Seconds_Count represents an elapsed time, measured in seconds, since the epoch. *)

Type sec_count = ``:num``

(* from Add manual: Time_Unit is an implementation-defined real number *)

val _ = Define `
 time_unit:real = ARB`



(* Time_First and Time_Last are the smallest and largest values of the Time type, respectively. *)

val _ = Define `
 time_first:time = ARB`

val _ = Define `
 time_last:time = ARB`


(* Time_Span_First and Time_Span_Last are the smallest and largest values
   of the Time_Span type, respectively *)

val _ = Define `
 time_span_first:time_span = ARB`

val _ = Define `
 time_span_last:time_span = ARB`


val _ = Define `
 time_span_zero:time_span = ARB`

val _ = Define `
 time_span_unit:time_span = ARB`


(* A clock tick is a real time interval during which the clock value
(as observed by calling the Clock function) remains constant. Tick is the average length of such intervals. *)

val _ = Define `
 tick:time_span = ARB`


(*
   The Time_Span value corresponding to the integer I represents
   the real-time duration I*Time_Unit *)

(* The Time value I represents the half-open real time interval
   that starts with E+I*Time_Unit and is limited by E+(I+1)*Time_Unit *)

(* half_open_interval a b = {x | a ≤ x ∧ x < b} *)

val _ = Define `
 time_value e i = {x | (e + i * time_unit) <= x /\ x < (e + (i+1) * time_unit)}`


(* TODO: gather them together later in one datatype, for time-based operations *)

(* functions for time-related types *)

(*
   we should support the function `Clock` from Ada.Real_time, this function reads the hardware clock
   (terminology: wall-clock), e.g.
    Start := Clock
    -- sequence of statements
    Finish := Clock
    if Finish - Start > Int.....

  It is clear that hardware clock is an external entity, that is read by a program, this could be implemented by
  an oracle similar as Call_FFI.
  We should not be using Call_FFI directly, since it represents somthing else and also takes ffi state

  we could use this:
     val _ = Datatype `
     clk_state =
     <| clock  : num option|>`;

  or, a simpler version is: *)

Type clock_state = ``: time``;  (* Can this clock ever be absent? :-)  *)

val _ = Define `
  add_time (t:time) (ts:time_span) = (ARB:time)`

val _ = Define `
  add_time' (ts:time_span) (t:time) = (ARB:time)`

val _ = Define `
  sub_time (t:time) (ts:time_span) = (ARB:time)`


val _ = Define `
  sub_time' (t:time) (ts:time) = (ARB:time_span)`

val _ = Define `
  lt_time (t:time) (t':time) = (ARB:bool)`

val _ = Define `
  leq_time (t:time) (t':time) = (ARB:bool)`

val _ = Define `
  gt_time (t:time) (t':time) = (ARB:bool)`

val _ = Define `
  gte_time (t:time) (t':time) = (ARB:bool)`


val _ = Define `
  add_tspan (ts:time_span) (ts':time_span) = (ARB:time_span)`

val _ = Define `
  sub_tspan (ts:time_span) (ts':time_span) = (ARB:time_span)`

val _ = Define `
  neg_tspan (ts:time_span) = (ARB:time_span)`


val _ = Define `
  mul_tspan (ts:time_span) (i:int) = (ARB:time_span)`

val _ = Define `
  mul_tspan' (i:int) (ts:time_span) = (ARB:time_span)`

val _ = Define `
  div_tspan (ts:time_span) (ts':time_span) = (ARB:int)`

val _ = Define `
  div_tspan' (ts:time_span) (i:int) = (ARB:time_span)`


val _ = Define `
  abs_time (ts:time_span) = (ARB:time_span)`

val _ = Define `
  lt_ts (t:time_span) (t':time_span) = (ARB:bool)`

val _ = Define `
  leq_ts (t:time_span) (t':time_span) = (ARB:bool)`


val _ = Define `
  gt_ts (t:time_span) (t':time_span) = (ARB:bool)`

val _ = Define `
  geq_ts (t:time_span) (t':time_span) = (ARB:bool)`

(*
  we might not be implementing these functions, as we are not supporting Duration
  function To_Duration (TS : Time_Span) return Duration;
  function To_Time_Span (D : Duration) return Time_Span;
*)


val _ = Define `
  Nanoseconds (n:int) = (ARB:time_span)`

val _ = Define `
  Microseconds (n:int) = (ARB:time_span)`

val _ = Define `
  Microseconds (n:int) = (ARB:time_span)`

val _ = Define `
  Seconds (n:int) = (ARB:time_span)`

val _ = Define `
  Minutes (n:int) = (ARB:time_span)`


(*
  procedure Split(T : in Time; SC : out Seconds_Count; TS : out Time_Span);
  function Time_Of(SC : Seconds_Count; TS : Time_Span) return Time;
*)

val _ = export_theory();
