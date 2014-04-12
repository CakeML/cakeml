(* OCaml: run fib 31 6 times *)


let input = 31;;
let result = 1346269;;

  exception Fail;;

  let rec fib x = 
    if x = 0 then 0 else if x = 1 then 1 else
      fib (x - 1) + fib (x - 2);;

  (*
  fun fib x = 
    case x of
         0 => 0
       | 1 => 1
       | n => fib (n - 1) + fib (n - 2);;
       *)

  let not x = if x then false else true;;

  let rec doit n =
    if n = 0 then 
      ()
    else 
      let _ = 
        if not (result = fib input) then
          raise Fail
        else ()
      in
      doit (n - 1);;
  let x = doit 6;;

