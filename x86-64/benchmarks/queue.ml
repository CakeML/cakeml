type 'a q = QUEUE of 'a list * 'a list;;

let empty = QUEUE ([],[]);;

let is_empty q =
  match q with
    (QUEUE ([],xs)) -> true
  | _ -> false;;

let rec reverse_aux l acc =
  match l with
    [] -> acc
  | (x::xs) -> reverse_aux xs (x::acc);;

let reverse xs = reverse_aux xs [];;

let checkf q =
  match q with
    (QUEUE ([],xs)) -> QUEUE (reverse xs,[])
  | _ -> q;;

let snoc q x =
  match q with
    (QUEUE (f,r)) -> checkf (QUEUE (f,x::r));;

let head q =
  match q with
    (QUEUE (x::f,r)) -> x
  | _ -> exit 1;;

let tail q =
  match q with
    (QUEUE (x::f,r)) -> checkf (QUEUE (f,r))
  | _ -> exit 1;;

let rec use_queue n q =
  if n = 0 then q else
    use_queue (n-1) (tail (snoc (snoc q (n-1)) (n-1)));;

let run_queue n = head (use_queue n empty);;

let test = run_queue 1000000;;
