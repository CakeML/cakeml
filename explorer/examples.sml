open HolKernel boolLib bossLib Parse astTheory terminationTheory sptreeTheory conLangProofTheory
open cakeml_computeLib progToBytecodeTheory bytecodeLabelsTheory
open Portable
open smpp 
(*Nested ifs*)
val ex1 = allIntermediates ``"exception Fail; val x = 5+4; if( (if(x>4 andalso x>5) then 5 else 4) > 3 ) then (if x>5 then 4 else 5) else (if x<2 orelse x>100 then 3 else raise Fail);"``;

(*Top lvl mutually recursive functions and function calls*)
val ex2 = allIntermediates ``"fun f x y = (g x) + (g y) and g x = x+1; f 5 4; g it;"``;

(*raise, handle and case*)
val ex3 = allIntermediates ``"exception Fail of int; exception Odd; exception Even; val x = 1; (case x of 1 => 2 | 2 => raise Even | 3 => raise Odd | _ => raise Fail 4) handle Odd => 1 | Even => 0+1+2+((raise Fail 5) handle Fail _ => 4) | Fail n => n;"``;

(*Structure defn*)
val ex4 = allIntermediates ``"structure Nat :> sig type nat val zero:nat val succ:nat-> nat end = struct datatype nat = Int of int val zero = Int 0 fun succ n = case n of Int x => Int (x+1) end;"``; 

(*Top lvl val, ref/deref*)
(*ex5 should parse wrongly*)
val ex5 = allIntermediates ``"val x = ref 5; x:= 1+!x;"``;

val ex6= allIntermediates ``"fun f y = let val x = ref y in x:= !x+1 end;"``;

(*datatypes, non exhausive pattern matching*)
val ex7 = allIntermediates ``"datatype 'a foo = Br of 'a * 'a foo * 'a foo | Lf of 'a | Nil; fun f x = case x of Br(v,l,r) => v + (f l) + (f r) | Lf v => v ; f (Br (1, Br(2,Lf 1, Lf 2), (Lf 1)));"``;

(*Pattern matching vals*)
val ex8 = allIntermediates ``"fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2));"``;

(*Datatype*)
val ex9 = allIntermediates ``"datatype foo = Br of ((int * string) * int) * string;"`` 

(*complex datatypes*)

val ex10 = allIntermediates ``"datatype ('a,'b,'c) foo2 = Foo of 'a * 'b | Foo2 of 'b * ('c * 'a->'b) | Foo3 of ('a*'b)*'c*('a,'a,'a) foo2;"``


(*Nested let vals*)

(*Inner lets*)

val ex11 = allIntermediates ``"val x = let fun f x = x + 1 val y = f 5 fun g z = y+1 and k y = g 1 val h = g 4 in let val k = 2 in k + f (f y) end end;"``;

val ex12 = allIntermediates ``"val x = let val y = (let val k = 4 in k+5 end) val z = 2 in let val k = 3 in k+z+y end end;"``;

(*Closures*)

val ex13 = allIntermediates ``"fun f x = (fn y => x+y); (if true then (f 2) else (f 3)) 3;"``

(*Nested letrec*)
val ex14 = allIntermediates ``"val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f end 3;"``

(*top level letrec*)
val ex15 = allIntermediates ``"fun fabracadabra x = gabracadabra (x-1) and gabracadabra x = if x = 0 then 1 else fabracadabra (x-1); fabracadabra 3;"``

(*Exceptions*)
val ex16 = allIntermediates ``"exception E of int*int->string*unit;"``

(*Datatypes*)
val ex17 = allIntermediates ``"datatype tree = Br of int * tree * tree | Lf;"``

(*Lists*)
val ex18 = allIntermediates ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val ex19 = allIntermediates ``"val x = \"hello\";"``;

val ex20 = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f n) end; (Nat.iter Nat.succ 5) Nat.zero;"``;

val ex21 = allIntermediates ``"structure Nat2 = struct val x = 1 val y=2 val z=3 fun f n = x+y+z+n end;"``;

val ex22 = allIntermediates ``"structure blablablabla :> sig type nat     datatype 'a blabla= Lf of 'a | Br of 'a blabla * 'a     val k : nat     val f : 'a blabla -> 'a blabla  end = struct     datatype nat = Int of int     datatype 'a blabla = Lf of 'a | Br of 'a blabla * 'a     val k = Int 0     fun f x = x end;"``;

val ex23 = allIntermediates ``"datatype foo = Lf of int * (int -> unit) * int| Br of (int * int) -> (unit * int);"``

val ex24 = allIntermediates ``"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f (n-1)) end;fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2)); (Nat.iter Nat.succ 5) Nat.zero;"``;

(*random semicolons in the struct, exceptions*)
val ex25 = allIntermediates ``"structure Nat :> sig val one:int; val zero:int end = struct val one = 1 ; val zero = 0 fun succ x y z = x+y+z+(if x>0 then one else zero); end; "``;

(*Exception ctors must start with uppercase*)
val ex26 = allIntermediates ``"structure Nat :> sig exception E end = struct exception E end; raise Nat.E;"``;

(*Word8, broken*)
val ex27 = allIntermediates ``"val x = 0wx5;"``;

(*pretty print for brackets*)
val ex28 = allIntermediates ``"val x = 1+2+3*4+5;"``;

val ex29 = allIntermediates ``"val x = (f y;if 5>4 then 3 else 2;let val x = 2 in 3 end;4;if(4<5) then 5 else f y);"``;

(*Type abbreviations*)
val ex30 = allIntermediates ``"type 'a nat = int*string*string*int*'a;"``

val ex31 = allIntermediates ``"structure Nat :> sig type nat; type nat2 = nat*nat; val zero:nat; val succ:nat->nat end = struct type nat = int; type nat2 = nat*nat; val zero = 5:nat end;"``

val ex32 = allIntermediates ``"type ('a,'b) compose = 'a -> 'b;"``;

val ex33 = allIntermediates ``"type t = exn`` 
