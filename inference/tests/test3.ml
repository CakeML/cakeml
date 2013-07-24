structure s :> sig  datatype 'a t = C of 'a; datatype ('a,'b,'c) t2 = D of 'a *
'b * 'c val g : 'a -> 'b -> 'c -> ('a,'b,'c) t2; val f : int -> int; end  =
struct
  datatype 'a t = C of 'a;
  datatype ('a,'b,'c) t2 = D of 'a * 'b * 'c;
  datatype u = E of int;
  fun f x = x;
  fun g x y z = D(x,y,z);
  val m = 4
end;

datatype t = C;

val l = s.f 2;
val l2 = s.C 1 = s.C 2;
val l3 = case s.C true of s.C x => if x then 1 else 2;
val l5 = s.g (s.C 1) true 4;
val l6 = case l5 of
  s.D(m1,m2,m3) => s.D(s.C 4, m2 andalso false, m3 + 11);


