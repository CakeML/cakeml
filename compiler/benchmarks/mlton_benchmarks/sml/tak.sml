fun tak (x,y,z) =
   if not (y < x)
      then z
   else tak (tak (x - 1, y, z),
             tak (y - 1, z, x),
             tak (z - 1, x, y))

val rec f =
   fn 0 => ()
    | n => (tak (33,22,11); f (n-1))

structure Main =
   struct
      val doit = f
   end

val foo = Main.doit 6;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
