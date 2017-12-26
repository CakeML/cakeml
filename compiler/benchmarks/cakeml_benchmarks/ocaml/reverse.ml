let rec reverse xs =
  let rec append xs ys =
    match xs with [] -> ys
    | (x::xs) -> x :: append xs ys in
  let rec rev xs =
    match xs with [] -> xs
    | (x::xs) -> append (rev xs) [x] in
  rev xs;;
let rec mk_list n =
  if (n = 0)
  then []
  else (n::(mk_list (n - 1)));;
let test = reverse (mk_list 50000);;


