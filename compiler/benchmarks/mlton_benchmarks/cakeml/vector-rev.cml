(* Written by Stephen Weeks (sweeks@sweeks.com). *)
exception Fail string;

structure Main =
   struct

      fun rev v =
         let
            val n = Vector.length v
         in
            Vector.tabulate n (fn i => Vector.sub v (n - 1 - i))
         end

      fun doit n =
         let
            val v = Vector.tabulate 200000 (fn i => i)
            fun loop n =
               if n < 0
                  then ()
               else
                  if 0 = Vector.sub (rev (rev v)) 0
                     then loop (n - 1)
                  else raise Fail "bug"
         in loop (n * 1000)
         end
   end

val foo = Main.doit 2
