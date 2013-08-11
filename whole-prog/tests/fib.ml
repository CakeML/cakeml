fun fib n = 
  if n = 0 then
    [0]
  else if n = 1 then
    [1,0]
  else
    case fib (n - 1) of
      f1::f2::fibs => f1+f2::f1::f2::fibs;

val fibs = fib 20;

val (f20::_) = fibs;
