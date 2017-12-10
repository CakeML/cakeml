fun fib n =
  if (n < 2)
  then n
  else ((fib (n - 1)) + (fib (n - 2)));
fun use_fib n =
  (((((fib n) + (fib n)) + (fib n)) + (fib n)) + (fib n)) + (fib n);
val test = use_fib 40;

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
val foo = writeInt test;
val u = CharIO.write #"\n";
*)
