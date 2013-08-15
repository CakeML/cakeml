  val input = 41;
  val result = 165580141;

  exception Fail;

  fun fib x = 
    if x = 0 then 0 else if x = 1 then 1 else
        fib (x - 1) + fib (x - 2);

  (*
  fun fib x = 
    case x of
         0 => 0
       | 1 => 1
       | n => fib (n - 1) + fib (n - 2);
       *)

  fun not x = if x then false else true;

  fun doit n =
    if n = 0 then 
      ()
    else 
      let val x = 
        if not (result = fib input) then
          raise Fail
        else ()
      in
        doit (n - 1)
      end;
  val x = doit 6;


