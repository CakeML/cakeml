let rec nbody x y z vx vy vz i =
  if i >= 100 then (x, y, z, vx, vy, vz)
  else
    let dt = 0.1 in
    let solarMass = 39.47841760435743 in
    let distance = sqrt(x *. x +. y *. y +. z *. z) in
    let mag = dt /. (distance *. distance *. distance) in
    let vxNew = vx -. x *. solarMass *. mag in
    let vyNew = vy -. y *. solarMass *. mag in
    let vzNew = vz -. z *. solarMass *. mag in

    let x1 = x +. dt *. vxNew in
    let y1 = y +. dt *. vyNew in
    let z1 = z +. dt *. vzNew in

    nbody x1 y1 z1 vxNew vyNew vzNew (i + 1);;


(* let () =
  let (x, y, z, vx, vy, vz) = nbody 1.6 3.4 2.3 0.1 0.1 0.1 0 in
  print_endline ("result: x = " ^ (string_of_float (x)) ^
    ", y = " ^ (string_of_float (y)) ^
    ", z = " ^ (string_of_float (z)));;
*)
