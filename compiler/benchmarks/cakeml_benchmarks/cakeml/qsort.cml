fun part p l (l1,l2) =
  case l
  of [] => (l1,l2)
  |  h::rst => (if (p h)
                then (part p rst (h::l1,l2))
                else (part p rst (l1,h::l2)));
fun partition p l = part p l ([],[]);
fun append l1 l2 =
  case l1
  of [] => l2
  |  x::xs => (x::(append xs l2));
fun qsort r l =
  case l
  of [] => []
  |  h::t => (case (partition (fn y => (r y h)) t)
              of (l1,l2) => (append (qsort r l1) (append [h] (qsort r l2))));
fun mk_list n =
  if (n = 0)
  then []
  else (n::(mk_list (n - 1)));
fun use_qsort n =
  qsort (fn x => (fn y => (x <= y))) (append (mk_list n) (mk_list n));
val test = use_qsort 10000;

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
val foo = map writeInt test;
val u = CharIO.write #"\n";
*)
