let swap i j arr =
  let ti = Array.get arr i in
  let tj = Array.get arr j in
  let d = Array.set arr i tj in
    Array.set arr j ti;;

let rec part_loop i j k arr =
  if i < j then
    (if Array.get arr i <= k then
         part_loop (i+1) j k arr
     else
       let u = swap i (j-1) arr in
         part_loop i (j-1) k arr)
  else i;;

let rec inplace_partition b e arr =
    let k = Array.get arr b in
    let i = part_loop (b+1) e k arr in
    let u = swap b (i-1) arr in
      i-1;;

let rec inplace_qsort b e arr =
    if b+1 < e then
      let i = inplace_partition b e arr in
      let u = inplace_qsort b i arr in
         inplace_qsort (i+1) e arr
    else ();;

let rec initarr len arr n =
  if n = len then
    arr
  else
    let u = Array.set arr n (len-n) in
    let u = Array.set arr (n+len) (len-n) in
        initarr len arr (n+1);;

let mkarr n = initarr n (Array.make (n+n) 0) 0;;

let foo = mkarr 20000;;

let test = inplace_qsort 0 40000 foo;;
