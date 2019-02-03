fun abs i = if i < 0 then ~i else i
exception Fail string

fun even' i = case i of
    0 => True
  | _ => odd' (i-1)
and odd'  i = case i of
    0 => False
  | _ => even' (i-1)

fun even i = even' (abs i)
fun odd i  = odd' (abs i)

structure Main =
   struct
      fun doit n =
         if n = 0
            then ()
         else let
                 val u = if (even 500000000) <> not (odd 500000000)
                            then raise Fail "bug"
                         else ()
              in
                 doit (n - 1)
              end
   end

val foo = Main.doit 10;
