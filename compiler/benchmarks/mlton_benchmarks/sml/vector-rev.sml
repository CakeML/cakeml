(* Written by Stephen Weeks (sweeks@sweeks.com). *)

structure Main =
   struct
      open Vector

      fun rev v =
         let
            val n = length v
         in
            tabulate (n, fn i => sub (v, n - 1 - i))
         end

      fun doit n =
         let
            val v = tabulate (200000, fn i => i)
            fun loop n =
               if n < 0
                  then ()
               else
                  if 0 = sub (rev (rev v), 0)
                     then loop (n - 1)
                  else raise Fail "bug"
         in loop (n * 1000)
         end
   end

val foo = Main.doit 2

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
