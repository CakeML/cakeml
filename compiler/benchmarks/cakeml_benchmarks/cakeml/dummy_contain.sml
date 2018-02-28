(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)
val with_inserts = false

fun insert1 a n l =
  if n < l then
    insert1 a (n + 6561) l
  else if n > l then
    insert1 a (n - l) l
  else
    ();

fun lookup1 a n l =
  if n < l then
    lookup1 a (n + 6561) l
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
let val a = Array.array 40000 0 in
  ins_look a 10000 40000
end;

val test = harness ();

