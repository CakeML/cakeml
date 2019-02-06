fun reverse xs =
  let
    fun append xs ys =
      case xs of [] => ys
      | (x::xs) => x :: append xs ys;
    fun rev xs =
      case xs of [] => xs
      | (x::xs) => append (rev xs) [x]
  in
    rev xs
  end;
fun mk_list n =
  if (n = 0)
  then []
  else (n::(mk_list (n - 1)));
val test = reverse (mk_list 50000);

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
