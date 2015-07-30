let print _ = ()

let fold xs f =
  let rec loop xs acc =
    match xs with
    | [] -> acc
    | x :: xs -> loop xs (f x acc)
  in
  loop xs

let naturalFold limit f =
  if limit < 0 then invalid_arg "naturalFold"
  else
    let rec loop i acc =
      if i = limit
        then acc
        else loop (i + 1) (f i acc)
    in
    loop 0

let naturalAny limit p =
  if limit < 0 then invalid_arg "naturalAny"
  else
    let rec loop i = i <> limit && (p i || loop (i + 1)) in
    loop 0

let naturalAll limit p =
  if limit < 0 then invalid_arg "naturalAll"
  else
    let rec loop i = i = limit || (p i && loop (i + 1)) in
    loop 0

type ('a, 'b) result = Ok of 'a | Bad of 'b

let return x = Ok x
let (>>=) x f =
  match x with
  | Ok r -> f r
  | Bad e -> Bad e

let foldOverPermutations u pf pacc f acc =
  let rec outer u pacc acc =
    match u with
    | [] -> f pacc acc
    | x :: xs ->
      let rec inner x xs revOut acc =
        let acc =
          match pf x pacc acc with
          | Ok (newPacc, acc) ->
            outer (fold revOut (fun x y -> x :: y) xs) newPacc acc
          | Bad acc -> acc
        in
        match xs with
        | [] -> acc
        | y :: ys -> inner y ys (x :: revOut) acc
      in
      inner x xs [] acc
  in
  outer u pacc acc
