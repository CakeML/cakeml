type time = Time.time

datatype 'a result = OK of 'a | Ex of exn

fun return (OK x) = x | return (Ex e) = raise e

fun time f x =
   let
      val timer = Timer.startRealTimer()
      val result = OK (f x) handle e => Ex e
      val timetaken = Timer.checkRealTimer timer
      val t = Time.toMilliseconds timetaken
      val decs = Int.toString ((t div 10) mod 100)
      val decs = if size decs < 1 then "00" else
                 if size decs < 2 then "0" ^ decs else decs
      val secs = Int.toString (t div 1000)


      val _ = print ("\ntime: "^secs^"."^decs^"\n")
   in
      result
   end


