val x = 10;

fun f x y z = if x then y else z;
val l3 = f true 1 2;

val l4 = let val x = 12 in x + x end;

fun l5 x = (10 + (raise IntError 4)) handle IntError n => n + x;

val l6 = (fn x => x) 1;

val l7 = let val r = ref 4 in r := !r + !r end;

val l8 = let fun even x = (x = 0) orelse (if x = 1 then false else odd (x - 1))
             and odd x = (x = 1) orelse (if x = 0 then false else even (x - 1))
           in
             even
         end;

val l9 = l8 3;
