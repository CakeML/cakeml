fun main() =
  let
  fun foldl f e xs =
    case xs of [] => e
    | (x::xs) => foldl f (f e x) xs;

  fun repeat x n =
    if (n = 0)
    then []
    else (x::(repeat x (n - 1)));

  val test = foldl (fn x => fn y => x + (foldl (fn x => fn y => x+y) 0 y)) 0
             (repeat (repeat 1 15000) 15000);
in () end;
