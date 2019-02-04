exception Fail string;

fun fib' n a b = case n of
    0 => a
  | _ => fib' (n-1) (a+b) a
fun fib n = fib' n 0 1

structure Main =
   struct
      fun doit() =
         if 701408733 <> fib 44
            then raise Fail "bug"
         else ()

      val doit =
        fn n =>
        let
          fun loop n =
            if n = 0
              then ()
              else (doit();loop(n-1))
        in loop (n * 1000000)
        end
   end

val foo = Main.doit 100;
