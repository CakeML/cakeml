let rec foldl f e xs =
  match xs with [] -> e
  | (x::xs) -> foldl f (f e x) xs;;

let rec repeat x n =
  if (n = 0)
  then []
  else (x::(repeat x (n - 1)));;

let test = foldl (fun x -> fun y -> x + (foldl (fun x -> fun y -> x+y) 0 y)) 0 (repeat (repeat 1 40000) 40000);;
