
val with_inserts = True

 fun  num_compare v1 =
   (fn  v2 =>
     if  (v1 = v2)
     then  Equal
      else  (if  (v1 < v2)
             then  Less
              else  Greater));

(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)
fun insert1 a n l =
  if n < l then
    (a := Map.insert num_compare n 1 (!a);
     insert1 a (n + 6561) l)
  else if n > l then
    insert1 a (n - l) l
  else
    ();

fun lookup1 a n l =
  if n < l then
    (Map.lookup num_compare n (!a);
     lookup1 a (n + 6561) l)
  else if n > l then
    lookup1 a (n - l) l
  else
    ();

fun ins_look a n len =
  if n = 0 then
    ()
  else
    ((if with_inserts then insert1 a 0 len else ()); lookup1 a 0 len; ins_look a (n - 1) len);

fun harness () =
let val a = Ref Tip in
  (insert1 a 0 40000;
   ins_look a 1000 40000)
end;


  val test = harness ();
