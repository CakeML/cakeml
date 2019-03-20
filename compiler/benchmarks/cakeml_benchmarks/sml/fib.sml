fun main ()=
  let
  fun fib n =
    if (n < 2)
    then n
    else ((fib (n - 1)) + (fib (n - 2)));
  fun use_fib n =
    (((((fib n) + (fib n)) + (fib n)) + (fib n)) + (fib n)) + (fib n);
  val test = use_fib 40;
in () end;

val _ = main();
(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
