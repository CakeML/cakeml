(* Naming things *)

val x = 1;
val x = true;
val y = false;
val y = x andalso y;

datatype t = C;
structure s = struct
  datatype t = C;
  val x = C;
          datatype u = D;
end;
datatype u = D;
val x = C;
val x = D;
