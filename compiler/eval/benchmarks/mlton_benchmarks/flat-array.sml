structure Main =
   struct
      fun doit n =
         let
            val v = Vector.tabulate_1 30000 (fn i => (i, i + 1))
            fun loop n =
               if 0 = n
                  then ()
               else
                  let
                     val sum = Vector.foldl_1
                       (fn c => fn (a, b) => a + b + c ) 0 v
                  in
                     loop (n - 1)
                  end
         in
            loop n
         end
   end

val foo = Main.doit 300000;
