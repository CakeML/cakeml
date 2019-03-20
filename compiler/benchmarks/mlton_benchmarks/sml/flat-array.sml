structure Main =
   struct
      fun doit n =
         let
            val v = Vector.tabulate (30000, fn i => (i, i + 1))
            fun loop n =
               if 0 = n
                  then ()
               else
                  let
                     val sum = Vector.foldl (fn ((a, b), c) =>
                                             a + b + c) 0 v
                  in
                     loop (n - 1)
                  end
         in
            loop n
         end
   end

val foo = Main.doit 25000;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
