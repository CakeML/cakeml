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

val test = nqueens 29 0 [];

(* I/O only
fun writeD d = CharIO.write (Char.chr (d+48));
fun digitInt n = if n >= 10 then (n mod 10) :: digitInt (n div 10) else [n];
fun map f l =
  case l
  of [] => []
  |  x::xs => let val v = (f x) in v::map f xs end;
fun reverse l acc =
  case l
  of [] => acc
  |  x::xs => reverse xs (x::acc);
fun writeInt n = map writeD (reverse (digitInt n) []);
val foo = map (fn p => case p of (x,y) => (writeInt x;CharIO.write #",";writeInt y;CharIO.write #"\n")) test;
val u = CharIO.write #"\n";
*)
