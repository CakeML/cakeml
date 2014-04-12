exception E;
exception F of int;

val x = ();
val y = 1;
val z = ~1;
fun f x = x;
val t = true;
val fl = false;
val b = (raise F 2;1) handle F x => x + 1;
val a = (if true then raise E else 1);
val m = 10;
