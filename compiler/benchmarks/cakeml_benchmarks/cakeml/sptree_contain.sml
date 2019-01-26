(* NB, 6561 (3^8) and 40000 (2^7 * 5^5) are chosen to be relatively prime so
 * that all element of the array are hit *)

val with_inserts = True

  datatype 'a sptree_spt =  Bs of  'a sptree_spt *  'a  *  'a sptree_spt
                         |  Bn of  'a sptree_spt *  'a sptree_spt
                         |  Ls of  'a
                          |  Ln;

  fun  lookup v7 v8 =
    case  v8
    of  Ln =>  None
    |   Ls(v1) =>  (if  (v7 <= 0)
                    then  (Some(v1))
                    else  None)
    |   Bn v3 v2  =>  (if  (v7 <= 0)
                       then  None
                        else  (lookup ((let val  k = v7 - 1
                                         in
                                          if  (k < 0)
                                          then  0
                                           else  k
                                         end) div 2) (if  (even v7)
                                                      then  v3
                                                       else  v2)))
    |   Bs v6 v5 v4  =>  (if  (v7 <= 0)
                          then  (Some(v5))
                          else  (lookup ((let val  k = v7 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end) div 2) (if  (even v7)
                                                        then  v6
                                                         else  v4)));

  fun  insert v7 v8 v9 =
    case  v9
    of  Ln =>  (if  (v7 <= 0)
                then  (Ls(v8))
                else  (if  (even v7)
                       then  (Bn(insert ((let val  k = v7 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end) div 2) v8 Ln) Ln)
                       else  (Bn Ln (insert ((let val  k = v7 - 1
                                              in
                                               if  (k < 0)
                                               then  0
                                                else  k
                                              end) div 2) v8 Ln))))
    |   Ls(v1) =>  (if  (v7 <= 0)
                    then  (Ls(v8))
                    else  (if  (even v7)
                           then  (Bs(insert ((let val  k = v7 - 1
                                               in
                                                if  (k < 0)
                                                then  0
                                                 else  k
                                               end) div 2) v8 Ln) v1 Ln)
                           else  (Bs Ln v1 (insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 Ln))))
    |   Bn v3 v2  =>  (if  (v7 <= 0)
                       then  (Bs v3 v8 v2)
                       else  (if  (even v7)
                              then  (Bn(insert ((let val  k = v7 - 1
                                                  in
                                                   if  (k < 0)
                                                   then  0
                                                    else  k
                                                  end) div 2) v8 v3)v2)
                              else  (Bn v3 (insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 v2))))
    |   Bs v6 v5 v4 =>  (if  (v7 <= 0)
                          then  (Bs v6 v8 v4)
                          else  (if  (even v7)
                                 then  (Bs(insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 v6)v5 v4)
                                 else  (Bs v6 v5 (insert ((let val  k =
                                                            v7 - 1
                                                           in
                                                            if  (k < 0)
                                                            then  0
                                                             else  k
                                                           end) div 2) v8 v4))));

fun insert1 a n l =
  if n < l then
    (a := insert n 1 (!a);
     insert1 a (n + 6561) l)
  else if n > l then
    insert1 a (n - l) l
  else
    ();

fun lookup1 a n l =
  if n < l then
    (lookup n (!a);
     lookup1 a (n + 6561) l)
  else if n > l then
    lookup1 a (n - l) l
  else
    ();

fun ins_look a n len =
  if n = 0 then
    ()
  else
    ((if with_inserts then insert1 a 0 len else ()); lookup1 a 0 len; ins_look a (n - 1) len);

fun harness () =
let val a = Ref Ln in
  (insert1 a 0 40000;
   ins_look a 1000 40000)
end;

val test = harness ();
