(* Written by Stephen Weeks (sweeks@sweeks.com). *)
exception Fail of string;

structure Main =
   struct
      fun doit n =
         let
            val len = 20000
            val sum = len * (len - 1)
            val v = Vector.tabulate_1 len (fn i => i)
            fun loop n =
               if n < 0
                  then ()
               else
                  if sum = Vector.foldl_1 (op +) 0 (Vector.concat_1 [v, v])
                     then loop (n - 1)
                  else raise Fail "bug"
         in loop (n * 10000)
         end
   end

val foo = Main.doit 32;
