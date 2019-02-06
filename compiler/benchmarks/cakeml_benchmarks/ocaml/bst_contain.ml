let with_inserts = false

 type ( 'k  ,  'w ) balanced_map_balanced_map =  Bin of  int *  'k  *  'w  *  ('k  ,  'w ) balanced_map_balanced_map *  ('k  ,  'w ) balanced_map_balanced_map
                                                  |  Tip
 type ternaryComparisons_ordering =  Greater
                                      |  Equal
                                      |  Less
let rec  lookup v6 v7 v8 =
   match  v8
   with  Tip ->  None
   |   Bin(v5,v4,v3,v2,v1) ->  (match  (v6 v7 v4)
                                with  Less ->  (lookup v6 v7 v2)
                                |   Equal ->  (Some(v3))
                                |   Greater ->  (lookup v6 v7 v1))
 let  singleton v1 =  (fun  v2 -> Bin(1,v1,v2,Tip,Tip))
 let  ratio = 2
 let  size v6 =
   match  v6
   with  Tip ->  0
   |   Bin(v5,v4,v3,v2,v1) ->  v5
 let  delta = 3
   let rec  balancel v41 =
   (fun  v42 ->
     (fun  v43 ->
       (fun  v44 ->
         match  v43
         with  Tip ->  (match  v44
                      with  Tip ->  (Bin(1,v41,v42,Tip,Tip))
                      |   (Bin(v5,v4,v3,v2,v1)) ->  (Bin(1 + v5,v41,v42,Tip,Bin(v5,v4,v3,v2,v1))))
         |   Bin(v40,v39,v38,v37,v36) ->  (match  v44
                                           with  Tip ->  (match  v37
                                                        with  Tip ->  (match  v36
                                                                     with  Tip ->  (Bin(2,v41,v42,Bin(v40,v39,v38,Tip,Tip),Tip))
                                                                     |   (Bin(v10,v9,v8,v7,v6)) ->  (Bin(3,v9,v8,Bin(1,v39,v38,Tip,Tip),Bin(1,v41,v42,Tip,Tip))))
                                                        |   (Bin(v20,v19,v18,v17,v16)) ->  (match  v36
                                                                                            with  Tip ->  (Bin(3,v39,v38,Bin(v20,v19,v18,v17,v16),Bin(1,v41,v42,Tip,Tip)))
                                                                                            |   (Bin(v15,v14,v13,v12,v11)) ->  (if  (v15 < (ratio * v20))
                                                                                                                                then  (Bin(1 + v40,v39,v38,Bin(v20,v19,v18,v17,v16),Bin(1 + v15,v41,v42,Bin(v15,v14,v13,v12,v11),Tip)))
                                                                                                                                else  (Bin(1 + v40,v14,v13,Bin((1 + v20) + (size v12),v39,v38,Bin(v20,v19,v18,v17,v16),v12),Bin(1 + (size v11),v41,v42,v11,Tip))))))
                                           |   (Bin(v35,v34,v33,v32,v31)) ->  (if  (v40 > (delta * v35))
                                                                               then  (match  v37
                                                                                      with  Tip ->  Tip
                                                                                      |   (Bin(v30,v29,v28,v27,v26)) ->  (match  v36
                                                                                                                          with  Tip ->  Tip
                                                                                                                          |   (Bin(v25,v24,v23,v22,v21)) ->  (if  (v25 < (ratio * v30))
                                                                                                                                                              then  (Bin((1 + v40) + v35,v39,v38,v37,Bin((1 + v35) + v25,v41,v42,v36,Bin(v35,v34,v33,v32,v31))))
                                                                                                                                                              else  (Bin((1 + v40) + v35,v24,v23,Bin((1 + v30) + (size v22),v39,v38,v37,v22),Bin((1 + v35) + (size v21),v41,v42,v21,Bin(v35,v34,v33,v32,v31)))))))
                                                                               else  (Bin((1 + v40) + v35,v41,v42,Bin(v40,v39,v38,v37,v36),Bin(v35,v34,v33,v32,v31))))))))

   let rec  balancer v41 =
   (fun  v42 ->
     (fun  v43 ->
       (fun  v44 ->
         match  v43
         with  Tip ->  (match  v44
                      with  Tip ->  (Bin(1,v41,v42,Tip,Tip))
                      |   (Bin(v20,v19,v18,v17,v16)) ->  (match  v17
                                                          with  Tip ->  (match  v16
                                                                       with  Tip ->  (Bin(2,v41,v42,Tip,Bin(v20,v19,v18,Tip,Tip)))
                                                                       |   (Bin(v5,v4,v3,v2,v1)) ->  (Bin(3,v19,v18,Bin(1,v41,v42,Tip,Tip),Bin(v5,v4,v3,v2,v1))))
                                                          |   (Bin(v15,v14,v13,v12,v11)) ->  (match  v16
                                                                                              with  Tip ->  (Bin(3,v14,v13,Bin(1,v41,v42,Tip,Tip),Bin(1,v19,v18,Tip,Tip)))
                                                                                              |   (Bin(v10,v9,v8,v7,v6)) ->  (if  (v15 < (ratio * v10))
                                                                                                                              then  (Bin(1 + v20,v19,v18,Bin(1 + v15,v41,v42,Tip,Bin(v15,v14,v13,v12,v11)),Bin(v10,v9,v8,v7,v6)))
                                                                                                                              else  (Bin(1 + v20,v14,v13,Bin(1 + (size v12),v41,v42,Tip,v12),Bin((1 + v10) + (size v11),v19,v18,v11,Bin(v10,v9,v8,v7,v6))))))))
         |   Bin(v40,v39,v38,v37,v36) ->  (match  v44
                                           with  Tip ->  (Bin(1 + v40,v41,v42,Bin(v40,v39,v38,v37,v36),Tip))
                                           |   (Bin(v35,v34,v33,v32,v31)) ->  (if  (v35 > (delta * v40))
                                                                               then  (match  v32
                                                                                      with  Tip ->  Tip
                                                                                      |   (Bin(v30,v29,v28,v27,v26)) ->  (match  v31
                                                                                                                          with  Tip ->  Tip
                                                                                                                          |   (Bin(v25,v24,v23,v22,v21)) ->  (if  (v30 < (ratio * v25))
                                                                                                                                                              then  (Bin((1 + v40) + v35,v34,v33,Bin((1 + v40) + v30,v41,v42,Bin(v40,v39,v38,v37,v36),v32),v31))
                                                                                                                                                              else  (Bin((1 + v40) + v35,v29,v28,Bin((1 + v40) + (size v27),v41,v42,Bin(v40,v39,v38,v37,v36),v27),Bin((1 + v25) + (size v26),v34,v33,v26,v31))))))
                                                                               else  (Bin((1 + v40) + v35,v41,v42,Bin(v40,v39,v38,v37,v36),Bin(v35,v34,v33,v32,v31))))))))

   let rec  insert v6 v7 v9 v8 =
   match  v8
   with  Tip ->  (singleton v7 v9)
   |   Bin(v5,v4,v3,v2,v1) ->  (match  (v6 v7 v4)
                                with  Less ->  (balancel v4 v3 (insert v6 v7 v9 v2) v1)
                                |   Equal ->  (Bin(v5,v7,v9,v2,v1))
                                |   Greater ->  (balancer v4 v3 v2 (insert v6 v7 v9 v1)))
 let  num_compare v1 =
   (fun  v2 ->
     if  (v1 = v2)
     then  Equal
      else  (if  (v1 < v2)
             then  Less
              else  Greater))

(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)
   let rec insert1 a n l =
  if n < l then
    (a := insert num_compare n 1 (!a);
     insert1 a (n + 6561) l)
  else if n > l then
    insert1 a (n - l) l
  else
    ()

  let rec lookup1 a n l =
  if n < l then
    (lookup num_compare n (!a);
     lookup1 a (n + 6561) l)
  else if n > l then
    lookup1 a (n - l) l
  else
    ()

  let rec ins_look a n len =
  if n = 0 then
    ()
  else
    ((if with_inserts then insert1 a 0 len else ()); lookup1 a 0 len; ins_look a (n - 1) len)

  let rec harness () =
let a = ref Tip in
  (insert1 a 0 40000;
   ins_look a 1000 40000)



  let test = harness ()
