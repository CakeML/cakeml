let print _ = ()

let fold xs f =
  let rec loop xs acc =
    match xs with
    | [] -> acc
    | x :: xs -> loop xs (f x acc)
  in
  loop xs

let rev = List.rev

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

let fmap f = function
  | Ok r -> Ok (f r)
  | Bad e -> Bad e
let (<*>) = function
  | Ok f -> (function
    | Ok x -> Ok (f x)
    | Bad e -> Bad e
    )
  | Bad e -> fun _ -> Bad e
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
        match pf x pacc acc with
        | Ok (newPacc, acc) ->
          let acc = outer (fold revOut (fun x y -> x :: y) xs) newPacc acc in
          (match xs with
          | [] -> acc
          | y :: ys -> inner y ys (x :: revOut) acc
          )
        | Bad acc -> acc
      in
      inner x xs [] acc
  in
  outer u pacc acc

let foldOverBagPerms u pf pacc f acc =
  let rec outer u pacc acc =
    match u with
    | [] -> f pacc acc
    | (x :: xclone) :: xs ->
      let rec inner xbag x xclone xs revOut acc =
        match pf x pacc acc with
        | Ok (newPacc, acc) ->
          let acc = outer (fold revOut (fun x y -> x :: y) (
            match xclone with
            | [] -> xs
            | _ -> xclone :: xs
            )) newPacc acc
          in
          (match xs with
          | [] -> acc
          | (y :: yclone) :: ys ->
            inner (y :: yclone) y yclone ys (xbag :: revOut) acc
          )
        | Bad acc -> acc
      in
      inner (x :: xclone) x xclone xs [] acc
  in
  outer u pacc acc

let foldOverSubsets u ef eacc f acc =
  let rec g x xs eacc isinc acc =
    match ef x isinc eacc acc with
    | Ok (newEacc, newAcc) -> outer xs newEacc newAcc
    | Bad acc -> acc
  and outer u eacc acc =
    match u with
    | [] -> f eacc acc
    | x :: xs -> let h = g x xs eacc in h false (h true acc)
  in
  outer u eacc acc

let f u =
  foldOverSubsets u
    (fun elem isinc set acc ->
     Ok ((if isinc then elem :: set else set), acc))
    [] (fun set sets -> set :: sets) []

let refine size classes connected =
  let sizeMatch x = naturalAll size
    (fun y -> connected size y = connected x (if y = x then size else y))
  in
  let merge cls (merged, classes) =
    if merged then
      true, rev cls :: classes
    else
      let x :: _ = cls in
      if sizeMatch x then
        true, fold cls (fun x y -> x :: y) [size] :: classes
      else
        false, rev cls :: classes
  in
  let split elem (yes, no) =
    if connected elem size then
      elem :: yes, no
    else
      yes, elem :: no
  in
  let subdivide cls acc =
    match cls with
    | [x] -> merge cls acc
    | _ ->
      match fold cls split ([], []) with
      | [], no -> merge no acc
      | yes, [] -> merge yes acc
      | yes, no -> merge no (merge yes acc)
  in
  match fold classes subdivide (false, []) with
  | true, classes -> rev classes
  | false, classes -> fold classes (fun x y -> x :: y) [[size]]

exception Fini

let minimal nverts classes connected =
  let perm = Array.make nverts (~-1) in
  let pf nw old acc =
    let rec loop v =
      if v = old then (
        Array.set perm old nw;
        Ok ((old + 1, acc)))
      else
        match connected old v, connected nw (Array.get perm v) with
        | true, false -> Bad acc
        | false, true -> raise Fini
        | _ -> loop (v + 1)
    in
    loop 0
  in
  let f _ acc = acc + 1 in
  try
    Some (foldOverBagPerms classes pf 0 f 0)
  with
  | Fini -> None

(*let foldOverGraphs ef eacc f acc =
  let makeVertss limit = Vector.tabulate *)
