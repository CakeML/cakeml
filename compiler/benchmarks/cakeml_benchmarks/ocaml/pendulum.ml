let sine x =
    x -. x *. x *. x /. 6.0 +. x *. x *. x *. x *. x /. 120.0;;

let rec pendulum t w n =
  if n = 0 then (t, w)
  else
    let h = 0.01 in
    let l = 2.0 in
    let g = 9.80665 in
    let k1t = w in
    let k1w = -. g /. l *. (sine t) in
    let k2t = w +. h /. 2.0 *. k1w in
    let k2w = -. g /. l *. (sine (t +. h /. 2.0 *. k1t)) in
    let tNew = t +. h *. k2t in
    let wNew = w +. h *. k2w in
    pendulum tNew wNew (n - 1);;

(* let () =
  let (tRes, wRes) = pendulum (-1.0) (-1.0) 5 in
  print_endline ("result: t = " ^ (string_of_float (tRes)) ^
    ", w = " ^ (string_of_float (wRes)));;
*)