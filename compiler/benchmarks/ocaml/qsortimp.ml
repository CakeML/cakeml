let swap i j arr =
  let ti = Array.get arr i in
  let tj = Array.get arr j in
  let d = Array.set arr i tj in
    Array.set arr j ti;;

let rec part_loop r i j k arr =
  if i < j then
    (if Array.get arr i <= k then
         part_loop r (i+1) j k arr
     else
       let u = swap i (j-1) arr in
         part_loop r i (j-1) k arr)
  else i;;

let rec inplace_partition r b e arr =
    let k = Array.get arr b in
    let i = part_loop r (b+1) e k arr in
    let u = swap b (i-1) arr in
      i-1;;

let rec inplace_qsort r b e arr =
    if b+1 < e then
      let i = inplace_partition r b e arr in
      let u = inplace_qsort r b i arr in
         inplace_qsort r (i+1) e arr
    else ();;

let rec initarr len arr n =
  if n = len then
    arr
  else
    let u = Array.set arr n (len-n,2) in
    let u = Array.set arr (n+len) (len-n,3) in
    let u = Array.set arr (n+2*len) (len-n,1) in
        initarr len arr (n+1);;

let mkarr n = initarr n (Array.make (n*3) (0,0)) 0;;

let foo = mkarr 20000;;

let test = inplace_qsort (fun (x,y) -> (fun (a,b) -> if x = a then y <= b else x<a)) 0 60000 foo;;

