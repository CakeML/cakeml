(* Concrete syntax for the benchmarks *)

val btree =
  let
  datatype tree = Leaf
                | Branch of tree * int * tree;
  fun insert x t =
    case t
    of Leaf => (Branch(Leaf,x,Leaf))
    |  Branch(t1,y,t2) => (if (x < y)
                           then (Branch(insert x t1,y,t2))
                           else (if (y < x)
                                 then (Branch(t1,y,insert x t2))
                                 else (Branch(t1,y,t2))));
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
    |  Branch(t1,x,t2) => (append (flatten t1) (append [x] (flatten t2)));
  fun tree_sort xs = flatten (build_tree xs);
  fun mk_list n =
    if (n = 0)
    then []
    else (n::(mk_list (n - 1)));
  fun use_tree n = tree_sort (append (mk_list n) (mk_list n));
  val test = use_tree 10000; in () end

val fib =
  let
  fun fib n =
    if (n < 2)
    then n
    else ((fib (n - 1)) + (fib (n - 2)));
  fun use_fib n =
    (((((fib n) + (fib n)) + (fib n)) + (fib n)) + (fib n)) + (fib n);
  val test = use_fib 36; in () end;

val queue =
  let
  datatype 'a q = QUEUE of 'a list * 'a list;
  val empty = QUEUE([],[]);
  fun is_empty q =
    case q
    of QUEUE([],xs) => true
    |  _ => false;
  fun reverse_aux l acc =
    case l
    of [] => acc
    |  x::xs => (reverse_aux xs (x::acc));
  fun reverse xs = reverse_aux xs [];
  fun checkf q =
    case q
    of QUEUE([],xs) => (QUEUE(reverse xs,[]))
    |  _ => q;
  fun snoc q x = case q of QUEUE(f,r) => (checkf (QUEUE(f,x::r)));
  fun head q = case q of QUEUE(x::f,r) => x;
  fun tail q = case q of QUEUE(x::f,r) => (checkf (QUEUE(f,r)));
  fun use_queue n q =
    if (n = 0)
    then q
    else (use_queue (n - 1) (tail (snoc (snoc q (n - 1)) (n - 1))));
  fun run_queue n = head (use_queue n empty);
  val test = run_queue 20000000; in () end;

val qsort =
  let
  fun part p l l1 l2 =
    case l
    of [] => (l1,l2)
    |  h::rst => (if (p h)
                  then (part p rst (h::l1) l2)
                  else (part p rst l1 (h::l2)));
  fun partition p l = part p l [] [];
  fun append l1 l2 =
    case l1
    of [] => l2
    |  x::xs => (x::(append xs l2));
  fun qsort r l =
    case l
    of [] => []
    |  h::t => (case (partition (fn y => (r y h)) t)
                of (l1,l2) => (append (qsort r l1) (append [h] (qsort r l2))));
  fun mk_list n =
    if (n = 0)
    then []
    else (n::(mk_list (n - 1)));
  fun use_qsort n =
    qsort (fn x => (fn y => (x <= y))) (append (mk_list n) (mk_list n));
  val test = use_qsort 10000; in () end;

val reverse =
  let
  fun reverse xs =
    let
      fun append xs ys =
        case xs of [] => ys
        | (x::xs) => x :: append xs ys;
      fun rev xs =
        case xs of [] => xs
        | (x::xs) => append (rev xs) [x]
    in
      rev xs
    end;
  fun mk_list n =
    if (n = 0)
    then []
    else (n::(mk_list (n - 1)));
  val test = reverse (mk_list 20000); in () end;

val foldl =
  let
  fun foldl f e xs =
    case xs of [] => e
    | (x::xs) => foldl f (f e x) xs;

  fun repeat x n =
    if (n = 0)
    then []
    else (x::(repeat x (n - 1)));

  val test = foldl (fn x => fn y => x + (foldl (fn x => fn y => x+y) 0 y)) 0
             (repeat (repeat 1 15000) 15000);
  in () end;


