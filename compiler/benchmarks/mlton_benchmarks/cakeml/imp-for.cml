exception Fail string;

fun for start stop f
  = let
      val i = Ref start
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
        val x = Ref 0

        val u = for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                for 0 10 (fn _ =>
                     x := !x + 1)))))))
      in
        if (!x) <> 10000000
          then raise Fail "bug"
          else ()
      end
  val doit = fn size => for 0 size (fn _ => doit ())
end

val foo = Main.doit 100;
