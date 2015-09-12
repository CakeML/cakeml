(* Translated from
   https://github.com/MLton/mlton/blob/master/benchmark/tests/fib.sml *)

let rec fib = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib (n - 1) + fib (n - 2)

module Main = struct
  let rec doit n =
    if n = 0 then
      ()
    else
      let _ = if 165580141 <> fib 41 then failwith "bug" else () in
      doit (n - 1)
end

let x = "Start"
let x = Main.doit 1
let x = "Stop"
