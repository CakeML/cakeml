datatype tree = Leaf
              | Branch of tree * int * tree;

fun insert x t =
  case t of
    Leaf => Branch (Leaf,x,Leaf)
  | (Branch (t1,y,t2)) =>
      if x < y then Branch (insert x t1,y,t2) else
      if y < x then Branch (t1,y,insert x t2) else
        Branch (t1,y,t2);

fun build_tree l =
  case l of
    [] => Leaf
  | (x::xs) => insert x (build_tree xs);

fun insert x t =
  case t of
    Leaf => Branch (Leaf,x,Leaf)
  | (Branch (t1,y,t2)) =>
      if x < y then Branch (insert x t1,y,t2) else
      if y < x then Branch (t1,y,insert x t2) else
        Branch (t1,y,t2);

fun build_tree l =
  case l of
    [] => Leaf
  | (x::xs) => insert x (build_tree xs);

fun append l ys =
  case l of
    [] => ys
  | (x::xs) => x :: append xs ys;

fun flatten t =
  case t of
    Leaf => []
  | (Branch (t1,x,t2)) => append (flatten t1) (append [x] (flatten t2));

fun tree_sort xs = flatten (build_tree xs);

fun mk_list n = if n = 0 then [] else n :: mk_list (n - 1);

fun use_tree n = tree_sort (append (mk_list n) (mk_list n));

val test = time use_tree 1000;
