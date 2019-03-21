
fun for (start, stop, f)
  = let
      val i = ref start
      fun loop () = if !i >= stop
                      then ()
                      else (f (!i) ; i := !i + 1 ; loop ())
    in
      loop ()
    end

structure Main =
struct
  fun doit ()
    = let
        val x = ref 0

        val _ = for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                for (0, 10, fn _ =>
                     x := !x + 1)))))))
      in
        if (!x) <> 10000000
          then raise Fail "bug"
          else ()
      end
  val doit = fn size => for (0, size, fn _ => doit ())
end

val foo = Main.doit 80;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
