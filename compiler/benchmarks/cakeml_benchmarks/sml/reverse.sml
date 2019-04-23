fun main ()=
  let
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
in () end;

val _ = main();
(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
