exception Fail;;

let rec abs x = if x < 0 then x else 0-x;;

(* equality version
let rec curcheck p ls =
    match ls with
      [] -> ()
    | (l::ls) ->
    match p with (x,y) ->
    match l with (a,b) ->
    if a = x || b = y || abs(a-x)=abs(b-y) then raise Fail else curcheck (x,y) ls;;
*)

let rec int_eq x y = (x <= y) && (y <= x);;

let rec curcheck p ls =
    match ls with
      [] -> ()
    | (l::ls) ->
    match p with (x,y) ->
    match l with (a,b) ->
    if int_eq a x || int_eq b y || int_eq (abs(a-x)) (abs(b-y)) then raise Fail else curcheck (x,y) ls;;

let rec nqueens n cur ls =
  if cur >= n then ls
  else
    let rec find_queen y =
      if y >= n then raise Fail
      else
      try (curcheck (cur,y) ls;nqueens n (cur+1) ((cur,y)::ls))
      with Fail -> find_queen (y+1)
    in
      find_queen 0;;

let foo = nqueens 29 0 [];;

