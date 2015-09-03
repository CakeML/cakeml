(* Tests for recursive non-function declarations. *)

type 'a stream = Cons of (unit -> 'a * 'a stream)

let zipWith f =
  let rec inner (Cons xf) (Cons yf) =
    let x, xs = xf () and y, ys = yf () in
    Cons (fun () -> f x y, inner xs ys)
  in
  inner

let tail (Cons xf) = let x, xs = xf () in xs

(*
let rec fibs =
  Cons (fun () -> 0, Cons (fun () -> 1, zipWith (+) fibs (tail fibs)))
*)
let fibs = let rec f a b = Cons (fun () -> a, f b (a + b)) in f 0 1

let rec at (Cons xf) =
  let x, xs = xf () in
  function
    | 0 -> x
    | n -> at xs (pred n)

let fib = at fibs

let rec falseTrue = Cons (fun () -> false, Cons (fun () -> true, falseTrue))

let rec zeroOne = Cons (fun () -> 0, oneZero)
    and oneZero = Cons (fun () -> 1, zeroOne)

let like b n =
  match b, n with
  | false, 0 | true, 1 -> true
  | _ -> false

let streamsLike = zipWith like falseTrue zeroOne

(* Taken from fib.ml *)
module Main = struct
  let rec doit n =
    if n = 0 then
      ()
    else
      let _ = if 165580141 <> fib 41 then failwith "fibs" in
      let _ = if not (at streamsLike n) then failwith "streamsLike" in
      doit (n - 1)
end

let x = "Start"
let x = Main.doit 1
let x = "Stop"
