type 'a q = QUEUE of 'a list * 'a list;;
let empty = QUEUE([],[]);;
let rec is_empty q =
  match q
  with QUEUE([],xs) -> true
  |  _ -> false;;
let rec reverse_aux l acc =
  match l
  with [] -> acc
  |  x::xs -> (reverse_aux xs (x::acc));;
let rec reverse xs = reverse_aux xs [];;
let rec checkf q =
  match q
  with QUEUE([],xs) -> (QUEUE(reverse xs,[]))
  |  _ -> q;;
let rec snoc q x = match q with QUEUE(f,r) -> (checkf (QUEUE(f,x::r)));;
let rec head q = match q with QUEUE(x::f,r) -> x;;
let rec tail q = match q with QUEUE(x::f,r) -> (checkf (QUEUE(f,r)));;
let rec use_queue n q =
  if (n = 0)
  then q
  else (use_queue (n - 1) (tail (snoc (snoc q (n - 1)) (n - 1))));;
let rec run_queue n = head (use_queue n empty);;
let test = run_queue 5000000;;


