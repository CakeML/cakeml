datatype tree = Leaf
              | Branch tree int tree;
fun insert x t =
  case t
  of Leaf => (Branch Leaf x Leaf)
  |  Branch t1 y t2 => (if (x < y)
                         then (Branch(insert x t1) y t2)
                         else (if (y < x)
                               then (Branch t1 y (insert x t2))
                               else (Branch t1 y t2)));
fun build_tree l =
  case l
  of [] => Leaf
  |  x::xs => (insert x (build_tree xs));
fun append l ys =
  case l
  of [] => ys
  |  x::xs => (x::(append xs ys));
fun flatten t =
  case t
  of Leaf => []
  |  Branch t1 x t2 => (append (flatten t1) (append [x] (flatten t2)));
fun tree_sort xs = flatten (build_tree xs);
fun mk_list n =
  if (n = 0)
  then []
  else (n::(mk_list (n - 1)));
fun use_tree n = tree_sort (append (mk_list n) (mk_list n));
val test = use_tree 20000;

(* I/O only
fun writeD d = CharIO.write (Char.chr (d+48));
fun digitInt n = if n >= 10 then (n mod 10) :: digitInt (n div 10) else [n];
fun map f l =
  case l
  of [] => []
  |  x::xs => let val v = (f x) in v::map f xs end;
fun reverse l acc =
  case l
  of [] => acc
  |  x::xs => reverse xs (x::acc);
fun writeInt n = map writeD (reverse (digitInt n) []);
val foo = map writeInt test;
val u = CharIO.write #"\n";
*)
