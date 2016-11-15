let swap i j arr =
  let ti = Array.get arr i in
  let tj = Array.get arr j in
  let d = Array.set arr i tj in
  let d  = Array.set arr j ti in
    arr;;

let rec part_loop i j k arr =
  if i < j then
    (if Array.get arr i <= k then
         part_loop (i+1) j k arr
     else
       let arr = swap i (j-1) arr in
         part_loop i (j-1) k arr)
  else (i,arr);;

let rec inplace_partition b e arr =
    let k = Array.get arr b in
    let res  = part_loop (b+1) e k arr in
        match res with (i,arr) ->
        let arr = swap b (i-1) arr in
          (i-1,arr);;

let rec inplace_qsort b e arr =
    if b+1 < e then
      let res  = inplace_partition b e arr in
          match res with (i,arr) ->
          let arr = inplace_qsort b i arr in
          let arr = inplace_qsort (i+1) e arr in
            arr
    else arr;;

let rec initarr len arr n =
  if n = len then
    arr
  else
    let u = Array.set arr n (len-n) in
    let u = Array.set arr (n+len) (len-n) in
        initarr len arr (n+1);;

let mkarr n = initarr n (Array.make (n+n) 0) 0;;

let test = inplace_qsort 0 40000 (mkarr 20000);;
