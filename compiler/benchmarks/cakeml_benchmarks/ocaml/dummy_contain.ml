let rec insert1 a n l =
  if n < l then
    insert1 a (n + 1) l
  else
    ()

let rec lookup1 a n l =
  if n < l then
    lookup1 a (n + 1) l
  else
    ()

let rec ins_look a n =
  if n = 0 then
    ()
  else
    (insert1 a 0 (Array.length a); lookup1 a 0 (Array.length a); ins_look a (n - 1))

let harness n =
let a = Array.make n 0 in
  ins_look a 500000

let test = harness 1000
