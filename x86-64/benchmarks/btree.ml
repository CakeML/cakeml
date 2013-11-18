type tree = Leaf
          | Branch of tree * int * tree;;

let rec insert x t =
  match t with
    Leaf -> Branch (Leaf,x,Leaf)
  | (Branch (t1,y,t2)) ->
      if x < y then Branch (insert x t1,y,t2) else
      if y < x then Branch (t1,y,insert x t2) else
        Branch (t1,y,t2);;

let rec build_tree l =
  match l with
    [] -> Leaf
  | (x::xs) -> insert x (build_tree xs);;

let rec insert x t =
  match t with
    Leaf -> Branch (Leaf,x,Leaf)
  | (Branch (t1,y,t2)) ->
      if x < y then Branch (insert x t1,y,t2) else
      if y < x then Branch (t1,y,insert x t2) else
        Branch (t1,y,t2);;

let rec build_tree l =
  match l with
    [] -> Leaf
  | (x::xs) -> insert x (build_tree xs);;

let rec append l ys =
  match l with
    [] -> ys
  | (x::xs) -> x :: append xs ys;;

let rec flatten t =
  match t with
    Leaf -> []
  | (Branch (t1,x,t2)) -> append (flatten t1) (append [x] (flatten t2));;

let tree_sort xs = flatten (build_tree xs);;

let rec mk_list n = if n = 0 then [] else n :: mk_list (n - 1);;

let use_tree n = tree_sort (append (mk_list n) (mk_list n));;

let test = use_tree 1000;;
