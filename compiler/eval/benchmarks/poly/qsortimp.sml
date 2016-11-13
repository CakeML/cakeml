fun main () =
  let
  fun swap (i,j,arr) =
    let val ti = Array.sub(arr,i)
        val tj = Array.sub(arr,j)
        val () = Array.update(arr,i,tj)
        val () = Array.update(arr,j,ti) in
          arr
    end;

  fun part_loop (i,j,k,arr) =
      if i < j then
        (if Array.sub(arr,i) <= k then
             part_loop (i+1,j,k,arr)
         else
           let val arr = swap(i,j-1,arr) in
             part_loop (i,j-1,k,arr)
           end)
      else (i,arr);

  fun inplace_partition (b,e,arr) =
      let val k = Array.sub(arr,b)
          val (i,arr) = part_loop (b+1,e,k,arr)
          val arr = swap(b,i-1,arr) in
            (i-1,arr)
          end;

  fun inplace_qsort (b,e,arr) =
      if b+1 < e then
        let val (i,arr) = inplace_partition (b,e,arr)
            val arr = inplace_qsort (b,i,arr)
            val arr = inplace_qsort (i+1,e,arr) in
              arr
            end
      else arr;

  fun initarr len arr n =
    if n = len then
      arr
    else
      let val _ = Array.update(arr,n,len-n)
          val _ = Array.update(arr,n+len,len-n) in
            initarr len arr (n+1)
          end

  fun mkarr n = initarr n (Array.array (n+n,0)) 0;

  val test = inplace_qsort(0,40000,mkarr 20000);

in () end;
