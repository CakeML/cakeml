val _ = PolyML.SaveState.loadState"heap";
val _ = use"html.sml";
val _ = use"pp.sml";

fun main() =
  let open Html
      fun genIntermediates src i =
        (test_location:=SOME ("Test"^Int.toString i^".html") ;
        printBody src (if src = "" then Nothing
        else Success(allIntermediates (stringSyntax.fromMLstring src))
        handle compilationError e => Error e
               | _ => Error "Unknown error"))
  in
  foldl (fn (x,y) => (genIntermediates x y;y+1)) 0 [

"val a = let val x = 5 val y = 4 fun f x = g x and g y = if(y<0) then y else f (y-1) val z = 3 in x+f y+ f z end;",

"[1,2,3,4,5];",

"val x = 5; [1,2,3,4,x];",

"val xs = [1,2,3,4]; 1::2::3::xs;",

"case [5] of (x::y::z) => x::z | _ => [];",

"exception Fail; val x = 5+4; if((if(x>4 andalso x>5) then 5 else 4) > 3 ) then (if x>5 then 4 else 5) else (if x<2 orelse x>100 then 3 else raise Fail);",

"fun f x y = (g x) + (g y) and g x = x+1; f 5 4; g it;",

"exception Fail of int; exception Odd; exception Even; val x = 1; (case x of 1 => 2 | 2 => raise Even | 3 => raise Odd | _ => raise Fail 4) handle Odd => 1 | Even => 0+1+2+((raise Fail 5) handle Fail _ => 4) | Fail n => n;",

"structure Nat :> sig type nat val zero:nat val succ:nat-> nat end = struct datatype nat = Int of int val zero = Int 0 fun succ n = case n of Int x => Int (x+1) end;",

"fun f y = let val x = ref y in x:= !x+1 end;",

"datatype 'a foo = Br of 'a * 'a foo * 'a foo | Lf of 'a | Nil; fun f x = case x of Br(v,l,r) => v + (f l) + (f r) | Lf v => v ; f (Br (1, Br(2,Lf 1, Lf 2), (Lf 1)));",

"fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2));",

"datatype foo = Br of ((int * string) * int) * string;",

"datatype ('a,'b,'c) foo2 = Foo of 'a * 'b | Foo2 of 'b * ('c * 'a->'b) | Foo3 of ('a*'b)*'c*('a,'a,'a) foo2;",

"val x = let fun f x = x + 1 val y = f 5 fun g z = y+1 and k y = g 1 val h = g 4 in let val k = 2 in k + f (f y) end end;",

"val x = let val y = (let val k = 4 in k+5 end) val z = 2 in let val k = 3 in k+z+y end end;",

"fun fabracadabra x = gabracadabra (x-1) and gabracadabra x = if x = 0 then 1 else fabracadabra (x-1); fabracadabra 3;",

"exception E of int*int->string*unit;",

"datatype tree = Br of int * tree * tree | Lf;",

"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];",

"val x = \"hello\";",

"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f n) end; (Nat.iter Nat.succ 5) Nat.zero;",

"structure Nat2 = struct val x = 1 val y=2 val z=3 fun f n = x+y+z+n end;",

"structure blablablabla :> sig type nat     datatype 'a blabla= Lf of 'a | Br of 'a blabla * 'a     val k : nat     val f : 'a blabla -> 'a blabla  end = struct     datatype nat = Int of int     datatype 'a blabla = Lf of 'a | Br of 'a blabla * 'a     val k = Int 0     fun f x = x end;",

"datatype foo = Lf of int * (int -> unit) * int| Br of (int * int) -> (unit * int);",

"structure Nat = struct val zero = 0 fun succ x = x+1 fun iter f n = if n = 0 then (fn x=> x) else f o (iter f (n-1)) end;fun f x y z= x+y+z; val (x,y,z) = (f 1 1 1,f 2 2 2,f (f (f 3 3 3) 1 2)); (Nat.iter Nat.succ 5) Nat.zero;",

(*random semicolons in the struct, exceptions*)
"structure Nat :> sig val one:int; val zero:int end = struct val one = 1 ; val zero = 0 fun succ x y z = x+y+z+(if x>0 then one else zero); end; ",

(*Exception ctors must start with uppercase*)
"structure Nat :> sig exception E end = struct exception E end; raise Nat.E;",

(*pretty print for brackets*)
"val x = 1+2+3*4+5;",

"val x = (f y;if 5>4 then 3 else 2;let val x = 2 in 3 end;4;if(4<5) then 5 else f y);",

(*Type abbreviations*)
"type 'a nat = int*string*string*int*'a;",

"structure Nat :> sig type nat; type nat2 = nat*nat; val zero:nat; val succ:nat->nat end = struct type nat = int; type nat2 = nat*nat; val zero = 5:nat end;",

"type ('a,'b) compose = 'a -> 'b;",

"type t = exn;"

]; ()
  end
