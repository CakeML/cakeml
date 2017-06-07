let rec fib n =
  if (n < 2)
  then n
  else ((fib (n - 1)) + (fib (n - 2)));;
let rec use_fib n =
  (((((fib n) + (fib n)) + (fib n)) + (fib n)) + (fib n)) + (fib n);;
let test = use_fib 40;;
