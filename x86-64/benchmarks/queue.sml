datatype 'a q = QUEUE of 'a list * 'a list;

val empty = QUEUE ([],[]);

fun is_empty q =
  case q of
    (QUEUE ([],xs)) => true
  | _ => false;

fun reverse_aux l acc =
  case l of
    [] => acc
  | (x::xs) => reverse_aux xs (x::acc);

fun reverse xs = reverse_aux xs [];

fun checkf q =
  case q of
    (QUEUE ([],xs)) => QUEUE (reverse xs,[])
  | _ => q;

fun snoc q x =
  case q of
    (QUEUE (f,r)) => checkf (QUEUE (f,x::r));

fun head q =
  case q of
    (QUEUE (x::f,r)) => x;

fun tail q =
  case q of
    (QUEUE (x::f,r)) => checkf (QUEUE (f,r));

fun use_queue n q =
  if n = 0 then q else
    use_queue (n-1) (tail (snoc (snoc q (n-1)) (n-1)));

fun run_queue n = head (use_queue n empty);

val test = time run_queue 1000000;
