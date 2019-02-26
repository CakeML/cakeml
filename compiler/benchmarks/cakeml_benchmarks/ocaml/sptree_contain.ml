(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)
let with_inserts = false

let even x = x mod 2 = 0

  type 'a sptree_spt =  Bs of  'a sptree_spt *  'a  *  'a sptree_spt
                         |  Bn of  'a sptree_spt *  'a sptree_spt
                         |  Ls of  'a
                     |  Ln


  let rec lookup v7 v8 =
    match  v8
    with  Ln ->  None
    |   Ls(v1) ->  (if  (v7 <= 0)
                    then  (Some(v1))
                    else  None)
    |   Bn(v3,v2) ->  (if  (v7 <= 0)
                       then  None
                        else  (lookup ((let k = v7 - 1
                                         in
                                          if  (k < 0)
                                          then  0
                                           else  k
                                         ) / 2) (if  (even v7)
                                                      then  v3
                                                       else  v2)))
    |   Bs(v6,v5,v4) ->  (if  (v7 <= 0)
                          then  (Some(v5))
                          else  (lookup ((let k = v7 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           ) / 2) (if  (even v7)
                                                        then  v6
                                                         else  v4)))

  let  rec insert v7 v8 v9 =
    match  v9
    with  Ln ->  (if  (v7 <= 0)
                then  (Ls(v8))
                else  (if  (even v7)
                       then  (Bn(insert ((let   k = v7 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           ) / 2) v8 Ln,Ln))
                       else  (Bn(Ln,insert ((let   k = v7 - 1
                                              in
                                               if  (k < 0)
                                               then  0
                                                else  k
                                              ) / 2) v8 Ln))))
    |   Ls(v1) ->  (if  (v7 <= 0)
                    then  (Ls(v8))
                    else  (if  (even v7)
                           then  (Bs(insert ((let   k = v7 - 1
                                               in
                                                if  (k < 0)
                                                then  0
                                                 else  k
                                               ) / 2) v8 Ln,v1,Ln))
                           else  (Bs(Ln,v1,insert ((let   k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     ) / 2) v8 Ln))))
    |   Bn(v3,v2) ->  (if  (v7 <= 0)
                       then  (Bs(v3,v8,v2))
                       else  (if  (even v7)
                              then  (Bn(insert ((let   k = v7 - 1
                                                  in
                                                   if  (k < 0)
                                                   then  0
                                                    else  k
                                                  ) / 2) v8 v3,v2))
                              else  (Bn(v3,insert ((let   k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     ) / 2) v8 v2))))
    |   Bs(v6,v5,v4) ->  (if  (v7 <= 0)
                          then  (Bs(v6,v8,v4))
                          else  (if  (even v7)
                                 then  (Bs(insert ((let   k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     ) / 2) v8 v6,v5,v4))
                                 else  (Bs(v6,v5,insert ((let   k =
                                                            v7 - 1
                                                           in
                                                            if  (k < 0)
                                                            then  0
                                                             else  k
                                                           ) / 2) v8 v4))))


let rec insert1 a n l =
  if n < l then
    (a := insert n 1 !a;
     insert1 a (n + 6561) l)
  else if n > l then
    insert1 a (n - l) l
  else
    ()

let rec lookup1 a n l =
  if n < l then
    (ignore (lookup n (!a));
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

let harness () =
let a = ref Ln in
  (insert1 a 0 40000;
   ins_look a 1000 40000)


let test = harness ()
