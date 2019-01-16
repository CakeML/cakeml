datatype 'a q = QUEUE of 'a list * 'a list;
val empty = QUEUE [] [];
fun is_empty q =
  case q
  of QUEUE [] xs => True
  |  _ => False;
fun reverse_aux l acc =
  case l
  of [] => acc
  |  x::xs => (reverse_aux xs (x::acc));
fun reverse xs = reverse_aux xs [];
fun checkf q =
  case q
  of QUEUE [] xs => (QUEUE(reverse xs) [])
  |  _ => q;
fun snoc q x = case q of QUEUE f r => (checkf (QUEUE f (x::r)));
fun head q = case q of QUEUE(x::f) r => x;
fun tail q = case q of QUEUE(x::f) r => (checkf (QUEUE f r));
fun use_queue n q =
  if (n = 0)
  then q
  else (use_queue (n - 1) (tail (snoc (snoc q (n - 1)) (n - 1))));
fun run_queue n = head (use_queue n empty);
val test = run_queue 5000000;

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
