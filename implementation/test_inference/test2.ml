(* List stuff *)
datatype 'a list = Nil | Cons of 'a * 'a list;

fun length x = 
  case x of
    Nil => 0
  | Cons (a, b) => 1 + length b;

val l1 = length Nil;
val l2 = length (Cons(1,Nil));
val l3 = length (Cons(true,Nil));

fun sum x =
 case x of
    Nil => 0
  | Cons (a, b) => a + length b;

val l2 = sum (Cons(1,Nil));

