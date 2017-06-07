fun swap i j arr =
  let val ti = Array.sub arr i
      val tj = Array.sub arr j
      val u = Array.update arr i tj in
        Array.update arr j ti
  end;

fun part_loop r i j k arr =
    if i < j then
      (if r (Array.sub arr i) k then
           part_loop r (i+1) j k arr
       else
         let val u = swap i (j-1) arr in
           part_loop r i (j-1) k arr
         end)
    else i;

fun inplace_partition r b e arr =
    let val k = Array.sub arr b
        val i = part_loop r (b+1) e k arr
        val arr = swap b (i-1) arr in
          i-1
        end;

fun inplace_qsort r b e arr =
    if b+1 < e then
      let val i = inplace_partition r b e arr
          val u = inplace_qsort r b i arr in
            inplace_qsort r (i+1) e arr
      end
    else ();

fun initarr len arr n =
  if n = len then
    arr
  else
    let val u = Array.update arr n ((len-n,2))
        val u = Array.update arr (n+len) ((len-n,3))
        val u = Array.update arr (n+2*len) ((len-n,1)) in
          initarr len arr (n+1)
        end;

fun mkarr n = initarr n (Array.array (n*3) (0,0)) 0;

val foo = mkarr 20000

val test = inplace_qsort (fn (x,y) => (fn (a,b) => if x = a then y <= b else x<a)) 0 60000 foo;
