let rec part p l l1 l2 =
  match l with
    [] -> (l1,l2)
  | (h::rst) -> if p h then part p rst (h::l1) l2
                       else part p rst l1 (h::l2);;

let partition p l = part p l [] [];;

let rec append l1 l2 =
  match l1 with
    [] -> l2
  | (x::xs) -> x :: (append xs l2);;

let rec qsort r l =
  match l with
    [] -> []
  | (h::t) -> let (l1,l2) = partition (fun y -> r y h) t in
                append (qsort r l1) (append [h] (qsort r l2));;

let rec mk_list n =
  if n = 0 then [] else n :: mk_list (n - 1);;

let use_qsort n =
  qsort (fun x -> fun y -> x <= y) (append (mk_list n) (mk_list n));;

let test = use_qsort 1000;;
