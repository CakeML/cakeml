fun main ()=
  let
  fun part p l (l1,l2) =
    case l
    of [] => (l1,l2)
    |  h::rst => (if (p h)
                  then (part p rst (h::l1,l2))
                  else (part p rst (l1,h::l2)));
  fun partition p l = part p l ([],[]);
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
  val test = use_qsort 10000;
in () end;
