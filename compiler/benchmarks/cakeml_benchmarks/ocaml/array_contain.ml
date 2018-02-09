(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)

let with_inserts = false

let rec insert1 a n l =
  if n < l then
    (Array.set a n 1;
     insert1 a (n + 6561) l)
  else if n > l then
    insert1 a (n - l) l
  else
    ()

let rec lookup1 a n l =
  if n < l then
    (Array.get a n;
     lookup1 a (n + 6561) l)
  else if n > l then
    lookup1 a (n - l) l
  else
    ()

let rec ins_look a n len =
  if n = 0 then
    ()
  else
    ((if with_inserts then insert1 a 0 len else ()); lookup1 a 0 len; ins_look a (n - 1) len)

let harness () =
let a = Array.make 40000 0 in
(insert1 a 0 40000;
 ins_look a 10000 40000)

let test = harness ()
