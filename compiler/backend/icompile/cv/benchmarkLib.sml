(*
	some bench marking tools
	*)

structure benchmarkLib =
struct

open preamble;

fun split_basis prog_name =
  let
    val prog_const = mk_const (prog_name, “: ast$dec list”);
    val basis = EVAL “TAKE 93 ^prog_const” |> rconc;
    val prog1 = EVAL “DROP 93 ^prog_const” |> rconc;
  in
    (basis, prog1)
  end;

local
   val second = Time.fromReal 1.0
   val minute = Time.fromReal 60.0
   val year0 = Date.year (Date.fromTimeUniv Time.zeroTime)
   fun to_str i u = if i = 0 then "" else Int.toString i ^ u
in
   fun time_to_string t =
      if Time.< (t, second)
         then Time.fmt 5 t ^ "s"
      else if Time.< (t, minute)
         then Time.fmt 1 t ^ "s"
      else let
              val d = Date.fromTimeUniv t
              val years = Date.year d - year0
              val days = Date.yearDay d
              val hours = Date.hour d
              val minutes = Date.minute d
           in
              if years + days + hours = 0 andalso minutes < 10 then
                 to_str minutes "m" ^ Date.fmt "%Ss" d
              else to_str years "y" ^ to_str days "d" ^ to_str hours "h" ^
                   Date.fmt "%Mm%Ss" d
           end
end;



fun start_time () = Timer.startCPUTimer ();

fun end_time_desc desc timer =
   let
      val {sys, usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
   in
      say ("runtime: " ^ time_to_string usr ^ ",\
       \    gctime: " ^ time_to_string gc ^ ", \
       \    systime: " ^ time_to_string sys ^ ". " ^ desc ^ "\n")
   end;

fun time_desc desc f x =
   let
      val timer = start_time ()
      val y = f x handle e => (end_time_desc desc timer; raise e)
   in
      end_time_desc desc timer; y
   end;
end;
   