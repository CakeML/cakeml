(* List stuff *)
datatype 'a lst = Nil | Cons of 'a * 'a lst;

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

datatype 'a option = NONE | SOME of 'a;
datatype ('a,'b) pair = Pair of 'a * 'b;

fun assoc k l = 
  case l of
      Nil => NONE
    | Cons (Pair(a,b),c) =>
        if k = l then
          SOME b
        else
          assoc k c;
        


