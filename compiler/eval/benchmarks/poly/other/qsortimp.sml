fun main () =
  let
  fun swap (i,j,arr) =
    let val ti = Array.sub(arr,i)
        val tj = Array.sub(arr,j)
        val u = Array.update(arr,i,tj)
        val u = Array.update(arr,j,ti) in
          ()
    end;

  fun part_loop (i,j,k,arr) =
      if i < j then
        (if Array.sub(arr,i) <= k then
             part_loop (i+1,j,k,arr)
         else
           let val u = swap(i,j-1,arr) in
             part_loop (i,j-1,k,arr)
           end)
      else i;

  fun inplace_partition (b,e,arr) =
      let val k = Array.sub(arr,b)
          val i = part_loop (b+1,e,k,arr)
          val u = swap(b,i-1,arr) in
            i-1
          end;

  fun inplace_qsort (b,e,arr) =
      if b+1 < e then
        let val i = inplace_partition (b,e,arr)
            val u = inplace_qsort (b,i,arr)
            val u = inplace_qsort (i+1,e,arr) in
              ()
            end
      else ();

  fun initarr len arr n =
    if n = len then
      arr
    else
      let val u = Array.update(arr,n,len-n)
          val u = Array.update(arr,n+len,len-n) in
            initarr len arr (n+1)
          end

  fun mkarr n = initarr n (Array.array (n+n,0)) 0;

  val arr = mkarr 20000;

  val test = inplace_qsort(0,40000,arr);
in () end;
