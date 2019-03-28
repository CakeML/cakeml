fun main ()=
  let
  exception Fail;

  fun abs x = if x < 0 then x else 0-x;

  fun curcheck p ls =
        case ls of
          [] => ()
        | (l::ls) =>
        case p of (x,y) =>
        case l of (a,b) =>
        if a = x orelse b = y orelse abs(a-x)=abs(b-y) then raise Fail else curcheck (x,y) ls;

  fun nqueens n cur ls =
    if cur >= n then ls
    else
      let fun find_queen y =
        if y >= n then raise Fail
        else
        (curcheck (cur,y) ls;nqueens n (cur+1) ((cur,y)::ls))
        handle Fail => find_queen (y+1)
      in
        find_queen 0
      end;

  val foo = nqueens 29 0 [];
in () end;

val _ = main();
(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
