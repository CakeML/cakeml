structure reg_alloc = struct

  type one = unit;

  fun  hd x1 =
    case  x1
    of  []  =>  (raise  Bind)
    |   v2::v1 =>  v2;

  fun  tl x1 =
    case  x1
    of  []  =>  (raise  Bind)
    |   v2::v1 =>  v1;

  fun  append v3 v4 =
    case  v3
    of  []  =>  v4
    |   v2::v1 =>  (v2::(append v1 v4));

  fun  rev v4 v3 =
    case  v4
    of  []  =>  v3
    |   v2::v1 =>  (rev v1 (v2::v3));

  fun  reverse v1 =  rev v1 [] ;

  fun  fst v3 =  case  v3 of  (v2,v1) =>  v2;

  fun  snd v3 =  case  v3 of  (v2,v1) =>  v1;

  fun  curry v1 =  (fn  v2 => (fn  v3 => v1 (v2,v3)));

  fun  uncurry v1 =  (fn  v2 => v1 (fst v2) (snd v2));

  fun  o_1 v2 =  (fn  v3 => (fn  v1 => v2 (v3 v1)));

  fun  i v1 =  v1;

  fun  c v3 =  (fn  v2 => (fn  v1 => v3 v1 v2));

  fun  k v2 =  (fn  v1 => v2);

  fun  s v3 =  (fn  v2 => (fn  v1 => v3 v1 (v2 v1)));

  fun  update v3 =
    (fn  v4 =>
      (fn  v2 =>
        (fn  v1 =>
          if  (v3 = v1)
          then  v4
           else  (v2 v1))));

  fun  w v2 =  (fn  v1 => v2 v1 v1);

  fun  the x1 =
    case  x1
    of  NONE =>  (raise  Bind)
    |   SOME(v1) =>  v1;

  fun  is_none v2 =
    case  v2
    of  NONE =>  (0 <= 0)
    |   SOME(v1) =>  (0 < 0);

  fun  is_some v2 =
    case  v2
    of  NONE =>  (0 < 0)
    |   SOME(v1) =>  (0 <= 0);

  fun  option_map v2 =
    (fn  v3 =>
      case  v3
      of  NONE =>  NONE
      |   SOME(v1) =>  (SOME(v2 v1)));

  fun  option_map2 v1 =
    (fn  v2 =>
      (fn  v3 =>
        if  ((is_some v2) andalso  (is_some v3))
        then  (SOME(v1 (the v2) (the v3)))
        else  NONE));

  datatype ( 'a  ,  'b ) sum =  Inr of  'b
                              |  Inl of  'a ;

  fun  isl v3 =
    case  v3
    of  Inl(v1) =>  (0 <= 0)
    |   Inr(v2) =>  (0 < 0);

  fun  isr v3 =
    case  v3
    of  Inl(v1) =>  (0 < 0)
    |   Inr(v2) =>  (0 <= 0);

  fun  outl x1 =
    case  x1
    of  Inl(v1) =>  v1
    |   Inr(v2) =>  (raise  Bind);

  fun  outr x1 =
    case  x1
    of  Inl(v1) =>  (raise  Bind)
    |   Inr(v2) =>  v2;

  fun  f v3 =
    (fn  v4 =>
      (fn  v5 =>
        case  v5
        of  Inl(v1) =>  (Inl(v3 v1))
        |   Inr(v2) =>  (Inr(v4 v2))));

  fun  length_aux v3 v4 =
    case  v3
    of  []  =>  v4
    |   v2::v1 =>  (length_aux v1 (v4 + 1));

  fun  length v1 =  length_aux v1 0;

  fun  map v3 v4 =
    case  v4
    of  []  =>  []
     |   v2::v1 =>  (v3 v2::(map v3 v1));

  fun  filter v3 v4 =
    case  v4
    of  []  =>  []
     |   v2::v1 =>  (if  (v3 v2)
                     then  (v2::(filter v3 v1))
                     else  (filter v3 v1));

  fun  foldr v4 v3 v5 =
    case  v5
    of  []  =>  v3
    |   v2::v1 =>  (v4 v2 (foldr v4 v3 v1));

  fun  foldl v4 v3 v5 =
    case  v5
    of  []  =>  v3
    |   v2::v1 =>  (foldl v4 (v4 v3 v2) v1);

  fun  sum v3 =
    case  v3
    of  []  =>  0
    |   v2::v1 =>  (v2 + (sum v1));

  fun  unzip v3 =
    case  v3
    of  []  =>  ([] ,[] )
    |   v2::v1 =>  (fst v2::(fst (unzip v1)),snd v2::(snd (unzip v1)));

  fun  flat v3 =
    case  v3
    of  []  =>  []
     |   v2::v1 =>  (append v2 (flat v1));

  fun  take v3 v4 =
    case  v4
    of  []  =>  []
     |   v2::v1 =>  (if  (v3 <= 0)
                     then  []
                      else  (v2::(take (let val  k = v3 - 1
                                         in
                                          if  (k < 0)
                                          then  0
                                           else  k
                                         end) v1)));

  fun  drop v3 v4 =
    case  v4
    of  []  =>  []
     |   v2::v1 =>  (if  (v3 <= 0)
                     then  (v2::v1)
                     else  (drop (let val  k = v3 - 1
                                   in
                                    if  (k < 0)
                                    then  0
                                     else  k
                                   end) v1));

  fun  snoc v4 v3 =
    case  v3
    of  []  =>  [v4]
    |   v2::v1 =>  (v2::(snoc v4 v1));

  fun  every v3 v4 =
    case  v4
    of  []  =>  (0 <= 0)
    |   v2::v1 =>  ((v3 v2) andalso  (every v3 v1));

  fun  exists v3 v4 =
    case  v4
    of  []  =>  (0 < 0)
    |   v2::v1 =>  ((v3 v2) orelse  (exists v3 v1));

  fun  genlist v1 v2 =
    if  (v2 <= 0)
    then  []
     else  (snoc (v1 (let val  k = v2 - 1
                       in
                        if  (k < 0)
                        then  0
                         else  k
                       end)) (genlist v1 (let val  k = v2 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end)));

  fun  pad_right v1 =
    (fn  v2 =>
      (fn  v3 =>
        append v3 (genlist (k v1) (let val  k = v2 - (length v3)
                                   in
                                     if  (k < 0)
                                     then  0
                                      else  k
                                    end))));

  fun  pad_left v1 =
    (fn  v2 =>
      (fn  v3 =>
        append (genlist (k v1) (let val  k = v2 - (length v3)
                                in
                                  if  (k < 0)
                                  then  0
                                   else  k
                                 end)) v3));

  fun  member v4 v3 =
    case  v3
    of  []  =>  (0 < 0)
    |   v2::v1 =>  ((v4 = v2) orelse  (member v4 v1));

  fun  all_distinct v3 =
    case  v3
    of  []  =>  (0 <= 0)
    |   v2::v1 =>  (((member v2 v1) = (0 < 0)) andalso  (all_distinct v1));

  fun  isprefix v5 v6 =
    case  v5
    of  []  =>  (0 <= 0)
    |   v4::v3 =>  (case  v6
                    of  []  =>  (0 < 0)
                    |   (v2::v1) =>  ((v4 = v2) andalso  (isprefix v3 v1)));

  fun  front x1 =
    case  x1
    of  []  =>  (raise  Bind)
    |   v2::v1 =>  (if  (v1 = [] )
                    then  []
                     else  (v2::(front v1)));

  fun  zip x1 =
    case  x1
    of  (v8,v7) =>  (case  v8
                     of  []  =>  (case  v7
                                  of  []  =>  []
                                   |   (v2::v1) =>  (raise  Bind))
                     |   (v6::v5) =>  (case  v7
                                       of  []  =>  (raise  Bind)
                                       |   (v4::v3) =>  ((v6,v4)::(zip (v5,v3)))));

  fun  el v2 v1 =
    if  (v2 <= 0)
    then  (hd v1)
    else  (el (let val  k = v2 - 1
                in
                 if  (k < 0)
                 then  0
                  else  k
                end) (tl v1));

  fun  last x1 =
    case  x1
    of  []  =>  (raise  Bind)
    |   v2::v1 =>  (if  (v1 = [] )
                    then  v2
                     else  (last v1));

  fun  splitatpki v6 v7 v8 =
    case  v8
    of  []  =>  (v7 [] [] )
    |   v5::v4 =>  (if  (v6 0 v5)
                    then  (v7 [] (v5::v4))
                    else  (splitatpki (o_1 v6 (fn  v1 =>
                                                (v1 + 1))) (fn  v3 =>
                                                             (fn  v2 =>
                                                               (v7 (v5::v3) v2))) v4));

  fun  part v3 v6 v4 v5 =
    case  v6
    of  []  =>  (v4,v5)
    |   v2::v1 =>  (if  (v3 v2)
                    then  (part v3 v1 (v2::v4) v5)
                    else  (part v3 v1 v4 (v2::v5)));

  fun  partition v1 =  (fn  v2 => part v1 v2 [] [] );

  fun  qsort v7 v8 =
    case  v8
    of  []  =>  []
     |   v6::v5 =>  (let val  v3 = partition (fn  v4 => (v7 v4 v6)) v5
                      in
                       case  v3
                       of  (v2,v1) =>  (append (append (qsort v7 v2) [v6]) (qsort v7 v1))
                     end);

  fun  exp_aux v2 v3 v1 =
    if  (v3 <= 0)
    then  v1
     else  (exp_aux v2 (let val  k = v3 - 1
                         in
                          if  (k < 0)
                          then  0
                           else  k
                         end) (v2 * v1));

  fun  exp v1 =  (fn  v2 => exp_aux v1 v2 1);

  fun  min v1 =
    (fn  v2 =>
      if  (v1 < v2)
      then  v1
       else  v2);

  fun  max v1 =
    (fn  v2 =>
      if  (v1 < v2)
      then  v2
       else  v1);

  fun  even v1 =  (v1 mod 2) <= 0;

  fun  odd v1 =  0 < (v1 mod 2);

  fun  funpow v1 v2 v3 =
    if  (v2 <= 0)
    then  v3
     else  (funpow v1 (let val  k = v2 - 1
                        in
                         if  (k < 0)
                         then  0
                          else  k
                        end) (v1 v3));

  fun  abs_diff v2 =
    (fn  v1 =>
      if  (v2 < v1)
      then  (let val  k = v1 - v2
              in
               if  (k < 0)
               then  0
                else  k
              end)
      else  (let val  k = v2 - v1
              in
               if  (k < 0)
               then  0
                else  k
              end));

  fun  pre v1 =
    let val  k = v1 - 1
     in
      if  (k < 0)
      then  0
       else  k
     end;

  fun  num_to_dec v1 =
    if  (v1 < 10)
    then  [Char.chr (48 + v1)]
    else  (Char.chr (48 + (v1 mod 10))::(num_to_dec (v1 div 10)));

  fun  num_to_dec_string v1 =  reverse (num_to_dec v1);

  fun  alookup v5 v6 =
    case  v5
    of  []  =>  NONE
    |   v4::v3 =>  (case  v4
                    of  (v2,v1) =>  (if  (v2 = v6)
                                     then  (SOME(v1))
                                     else  (alookup v3 v6)));

  fun  aupdate v3 =  (fn  v4 => case  v4 of  (v2,v1) =>  ((v2,v1)::v3));

  fun  aevery_aux v5 v6 v7 =
    case  v7
    of  []  =>  (0 <= 0)
    |   v4::v3 =>  (case  v4
                    of  (v2,v1) =>  (if  (member v2 v5)
                                     then  (aevery_aux v5 v6 v3)
                                     else  ((v6 (v2,v1)) andalso  (aevery_aux (v2::v5) v6 v3))));

  fun  aevery v1 =  aevery_aux [] v1;

  fun  amap v5 v6 =
    case  v6
    of  []  =>  []
     |   v4::v3 =>  (case  v4 of  (v2,v1) =>  ((v2,v5 v1)::(amap v5 v3)));

  fun  adel v5 v6 =
    case  v5
    of  []  =>  []
     |   v4::v3 =>  (case  v4
                     of  (v2,v1) =>  (if  (v2 = v6)
                                      then  (adel v3 v6)
                                      else  ((v2,v1)::(adel v3 v6))));

  fun  while_1 v1 v2 v3 =
    if  (v1 v3)
    then  (while_1 v1 v2 (v2 v3))
    else  v3;

  fun  owhile v1 v2 v3 =
    if  (v1 v3)
    then  (owhile v1 v2 (v2 v3))
    else  (SOME(v3));

  fun  least v3 =
    while_1 (fn  v1 => ((v3 v1) = (0 < 0))) (fn  v2 => (v2 + 1)) 0;

  datatype 'a sptree_spt =  Bs of  'a sptree_spt *  'a  *  'a sptree_spt
                         |  Bn of  'a sptree_spt *  'a sptree_spt
                         |  Ls of  'a
                          |  Ln;

  datatype reg_alloc_ra_state =  Recordtypera_state of  one sptree_spt sptree_spt *  int *  int sptree_spt *  int list *  int list *  int list *  int list *  int sptree_spt *  one sptree_spt *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  int;

  fun  ra_state_graph v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v13;

  fun  ra_state_colours v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v12;

  fun  ra_state_degs v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v11;

  fun  ra_state_simp_worklist v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v10;

  fun  ra_state_freeze_worklist v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v9;

  fun  ra_state_spill_worklist v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v8;

  fun  ra_state_stack v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v7;

  fun  ra_state_coalesced v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v6;

  fun  ra_state_move_related v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v5;

  fun  ra_state_avail_moves_pri v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v4;

  fun  ra_state_avail_moves v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v3;

  fun  ra_state_unavail_moves v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v2;

  fun  ra_state_clock v14 =
    case  v14
    of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v1;

  fun  ra_state_graph_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v14 v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_colours_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v14 v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_degs_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v14 v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_simp_worklist_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v14 v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_freeze_worklist_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v14 v9,v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_spill_worklist_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v14 v8,v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_stack_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v14 v7,v6,v5,v4,v3,v2,v1)));

  fun  ra_state_coalesced_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v14 v6,v5,v4,v3,v2,v1)));

  fun  ra_state_move_related_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v14 v5,v4,v3,v2,v1)));

  fun  ra_state_avail_moves_pri_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v14 v4,v3,v2,v1)));

  fun  ra_state_avail_moves_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v14 v3,v2,v1)));

  fun  ra_state_unavail_moves_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v14 v2,v1)));

  fun  ra_state_clock_fupd v14 =
    (fn  v15 =>
      case  v15
      of  Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v14 v1)));

  fun  bind v5 =
    (fn  v4 => o_1 (fn  v3 => (case  v3 of  (v2,v1) =>  (v4 v2 v1))) v5);

  fun  unit v2 =  (fn  v1 => (v2,v1));

  fun  get_clock v1 =  unit (ra_state_clock v1) v1;

  fun  has_work v2 =  bind get_clock (fn  v1 => (unit (v1 > 0))) v2;

  fun  ignore_bind v2 =  (fn  v3 => bind v2 (fn  v1 => v3));

  fun  dec_clock v1 =
    ((),ra_state_clock_fupd (k (let val  k = (ra_state_clock v1) - 1
                                 in
                                  if  (k < 0)
                                  then  0
                                   else  k
                                 end)) v1);

  fun  get_simp_worklist v1 =  unit (ra_state_simp_worklist v1) v1;

  fun  set_simp_worklist v2 =
    (fn  v1 => ((),ra_state_simp_worklist_fupd (k v2) v1));

  fun  get_graph v1 =  unit (ra_state_graph v1) v1;

  fun  lookup v7 v8 =
    case  v8
    of  Ln =>  NONE
    |   Ls(v1) =>  (if  (v7 <= 0)
                    then  (SOME(v1))
                    else  NONE)
    |   Bn(v3,v2) =>  (if  (v7 <= 0)
                       then  NONE
                        else  (lookup ((let val  k = v7 - 1
                                         in
                                          if  (k < 0)
                                          then  0
                                           else  k
                                         end) div 2) (if  (even v7)
                                                      then  v3
                                                       else  v2)))
    |   Bs(v6,v5,v4) =>  (if  (v7 <= 0)
                          then  (SOME(v5))
                          else  (lookup ((let val  k = v7 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end) div 2) (if  (even v7)
                                                        then  v6
                                                         else  v4)));

  fun  lrnext v1 =
    if  (v1 <= 0)
    then  1
     else  (2 * (lrnext ((let val  k = v1 - 1
                           in
                            if  (k < 0)
                            then  0
                             else  k
                           end) div 2)));

  fun  foldi v9 v10 v12 v11 =
    case  v11
    of  Ln =>  v12
    |   Ls(v1) =>  (v9 v10 v1 v12)
    |   Bn(v4,v3) =>  (let val  v2 = lrnext v10
                        in
                         foldi v9 (v10 + v2) (foldi v9 (v10 + (2 * v2)) v12 v4) v3
                        end)
    |   Bs(v8,v7,v6) =>  (let val  v5 = lrnext v10
                           in
                            foldi v9 (v10 + v5) (v9 v10 v7 (foldi v9 (v10 + (2 * v5)) v12 v8)) v6
                           end);

  fun  toalist v4 =
    foldi (fn  v3 => (fn  v2 => (fn  v1 => ((v3,v2)::v1)))) 0 [] v4;

  fun  foreach v6 =
    case  v6
    of  (v5,v4) =>  (case  v5
                     of  []  =>  (unit ())
                     |   (v3::v2) =>  (bind (v4 v3) (fn  v1 =>
                                                      (foreach (v2,v4)))));

  fun  get_deg v2 =  (fn  v1 => unit (lookup v2 (ra_state_degs v1)) v1);

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
                                           end) div 2) v8 Ln,Ln))
                       else  (Bn(Ln,insert ((let val  k = v7 - 1
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
                                               end) div 2) v8 Ln,v1,Ln))
                           else  (Bs(Ln,v1,insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 Ln))))
    |   Bn(v3,v2) =>  (if  (v7 <= 0)
                       then  (Bs(v3,v8,v2))
                       else  (if  (even v7)
                              then  (Bn(insert ((let val  k = v7 - 1
                                                  in
                                                   if  (k < 0)
                                                   then  0
                                                    else  k
                                                  end) div 2) v8 v3,v2))
                              else  (Bn(v3,insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 v2))))
    |   Bs(v6,v5,v4) =>  (if  (v7 <= 0)
                          then  (Bs(v6,v8,v4))
                          else  (if  (even v7)
                                 then  (Bs(insert ((let val  k = v7 - 1
                                                     in
                                                      if  (k < 0)
                                                      then  0
                                                       else  k
                                                     end) div 2) v8 v6,v5,v4))
                                 else  (Bs(v6,v5,insert ((let val  k =
                                                            v7 - 1
                                                           in
                                                            if  (k < 0)
                                                            then  0
                                                             else  k
                                                           end) div 2) v8 v4))));

  fun  set_deg v2 =
    (fn  v3 =>
      (fn  v1 =>
        ((),ra_state_degs_fupd (k (insert v2 v3 (ra_state_degs v1))) v1)));

  fun  dec_one v3 =
    bind (get_deg v3) (fn  v2 =>
                        (case  v2
                         of  NONE =>  (unit ())
                         |   (SOME(v1)) =>  (set_deg v3 (let val  k =
                                                           v1 - 1
                                                          in
                                                           if  (k < 0)
                                                           then  0
                                                            else  k
                                                          end))));

  fun  dec_deg v4 =
    bind get_graph (fn  v3 =>
                     (case  (lookup v4 v3)
                      of  NONE =>  (unit ())
                      |   (SOME(v2)) =>  (let val  v1 =
                                            map fst (toalist v2)
                                          in
                                            foreach (v1,dec_one)
                                          end)));

  fun  get_spill_worklist v1 =  unit (ra_state_spill_worklist v1) v1;

  fun  get_degs v1 =  unit (ra_state_degs v1) v1;

  fun  get_colours v1 =  unit (ra_state_colours v1) v1;

  fun  get_move_rel v1 =  unit (ra_state_move_related v1) v1;

  fun  get_unavail_moves v1 =  unit (ra_state_unavail_moves v1) v1;

  fun  split_priority v6 =
    partition (fn  v5 =>
                (case  v5
                 of  (v4,v3) =>  (case  v3 of  (v2,v1) =>  (v4 > 0)))) v6;

  fun  add_avail_moves_pri v2 =
    (fn  v1 =>
      ((),ra_state_avail_moves_pri_fupd (k (append v2 (ra_state_avail_moves_pri v1))) v1));

  fun  add_avail_moves v2 =
    (fn  v1 =>
      ((),ra_state_avail_moves_fupd (k (append v2 (ra_state_avail_moves v1))) v1));

  fun  set_unavail_moves v2 =
    (fn  v1 => ((),ra_state_unavail_moves_fupd (k v2) v1));

  fun  revive_moves v16 =
    bind get_graph (fn  v15 =>
                     (case  (lookup v16 v15)
                      of  NONE =>  (unit ())
                      |   (SOME(v14)) =>  (let val  v13 =
                                             v16::(map fst (toalist v14))
                                           in
                                             bind get_unavail_moves (fn  v12 =>
                                                                      (let val  v6 =
                                                                         partition (fn  v11 =>
                                                                                     (case  v11
                                                                                      of  (v10,v9) =>  (case  v9
                                                                                                        of  (v8,v7) =>  ((member v8 v13) orelse  (member v7 v13))))) v12
                                                                        in
                                                                         case  v6
                                                                         of  (v5,v4) =>  (let val  v3 =
                                                                                            split_priority v5
                                                                                           in
                                                                                            case  v3
                                                                                            of  (v2,v1) =>  (ignore_bind (add_avail_moves_pri v2) (ignore_bind (add_avail_moves v1) (set_unavail_moves v4)))
                                                                                          end)
                                                                       end))
                                           end)));

  fun  set_spill_worklist v2 =
    (fn  v1 => ((),ra_state_spill_worklist_fupd (k v2) v1));

  fun  add_simp_worklist v2 =
    (fn  v1 =>
      ((),ra_state_simp_worklist_fupd (k (append v2 (ra_state_simp_worklist v1))) v1));

  fun  add_freeze_worklist v2 =
    (fn  v1 =>
      ((),ra_state_freeze_worklist_fupd (k (append v2 (ra_state_freeze_worklist v1))) v1));

  fun  unspill v14 =
    bind get_spill_worklist (fn  v13 =>
                              (bind get_degs (fn  v12 =>
                                               (bind get_colours (fn  v11 =>
                                                                   (bind get_move_rel (fn  v10 =>
                                                                                        (let val  v7 =
                                                                                           partition (fn  v9 =>
                                                                                                       (case  (lookup v9 v12)
                                                                                                        of  NONE =>  (0 < 0)
                                                                                                        |   (SOME(v8)) =>  (v8 < v11))) v13
                                                                                          in
                                                                                           case  v7
                                                                                           of  (v6,v5) =>  (let val  v3 =
                                                                                                              partition (fn  v4 =>
                                                                                                                          ((lookup v4 v10) = (let val  x =
                                                                                                                                                ()
                                                                                                                                              in
                                                                                                                                                SOME(x)
                                                                                                                                              end))) v6
                                                                                                             in
                                                                                                              case  v3
                                                                                                              of  (v2,v1) =>  (ignore_bind (foreach (v6,revive_moves)) (ignore_bind (set_spill_worklist v5) (ignore_bind (add_simp_worklist v1) (add_freeze_worklist v2))))
                                                                                                            end)
                                                                                         end)))))))) v14;

  fun  simplify v4 =
    bind get_simp_worklist (fn  v3 =>
                             (case  v3
                              of  []  =>  (unit NONE)
                              |   (v2::v1) =>  (ignore_bind (set_simp_worklist v1) (ignore_bind (dec_deg v2) (ignore_bind unspill (unit (SOME(v2)))))))) v4;

  fun  get_avail_moves_pri v1 =  unit (ra_state_avail_moves_pri v1) v1;

  fun  split_avail v3 v4 v6 v5 =
    case  v6
    of  []  =>  (NONE,(v5,[] ))
    |   v2::v1 =>  (if  (v3 v2)
                    then  (if  (v4 v2)
                           then  (SOME(v2),(v5,v1))
                           else  (split_avail v3 v4 v1 (v2::v5)))
                    else  (split_avail v3 v4 v1 v5));

  fun  lookup_g v3 =
    (fn  v4 =>
      (fn  v2 =>
        case  (lookup v3 v2)
        of  NONE =>  (0 < 0)
        |   SOME(v1) =>  ((lookup v4 v1) = (let val  x = ()
                                            in
                                              SOME(x)
                                            end))));

  fun  is_phy_var v1 =  (v1 mod 2) <= 0;

  fun  is_valid_move v6 =
    (fn  v8 =>
      (fn  v7 =>
        let val  v5 = v7
         in
          case  v5
          of  (v4,v3) =>  (case  v3
                           of  (v2,v1) =>  ((((v2 = v1) = (0 < 0)) andalso  ((lookup_g v2 v1 v6) = (0 < 0))) andalso  (if  (is_phy_var v2)
                                                                                                                       then  ((lookup v1 v8) = (let val  x =
                                                                                                                                                  ()
                                                                                                                                                in
                                                                                                                                                  SOME(x)
                                                                                                                                                end))
                                                                                                                       else  ((((is_phy_var v1) = (0 < 0)) andalso  ((lookup v1 v8) = (let val  x =
                                                                                                                                                                                         ()
                                                                                                                                                                                       in
                                                                                                                                                                                         SOME(x)
                                                                                                                                                                                       end))) andalso  ((lookup v2 v8) = (let val  x =
                                                                                                                                                                                                                            ()
                                                                                                                                                                                                                          in
                                                                                                                                                                                                                            SOME(x)
                                                                                                                                                                                                                          end))))))
        end));

  fun  mk_bn v13 =
    (fn  v14 =>
      case  v13
      of  Ln =>  (case  v14
                  of  Ln =>  Ln
                  |   (Ls(v1)) =>  (Bn(Ln,Ls(v1)))
                  |   (Bn(v3,v2)) =>  (Bn(Ln,Bn(v3,v2)))
                  |   (Bs(v6,v5,v4)) =>  (Bn(Ln,Bs(v6,v5,v4))))
      |   Ls(v7) =>  (Bn(Ls(v7),v14))
      |   Bn(v9,v8) =>  (Bn(Bn(v9,v8),v14))
      |   Bs(v12,v11,v10) =>  (Bn(Bs(v12,v11,v10),v14)));

  fun  mk_bs v13 =
    (fn  v14 =>
      (fn  v15 =>
        case  v15
        of  Ln =>  (case  v13
                    of  Ln =>  (Ls(v14))
                    |   (Ls(v1)) =>  (Bs(Ls(v1),v14,Ln))
                    |   (Bn(v3,v2)) =>  (Bs(Bn(v3,v2),v14,Ln))
                    |   (Bs(v6,v5,v4)) =>  (Bs(Bs(v6,v5,v4),v14,Ln)))
        |   Ls(v7) =>  (Bs(v13,v14,Ls(v7)))
        |   Bn(v9,v8) =>  (Bs(v13,v14,Bn(v9,v8)))
        |   Bs(v12,v11,v10) =>  (Bs(v13,v14,Bs(v12,v11,v10)))));

  fun  difference v25 v26 =
    case  v25
    of  Ln =>  Ln
    |   Ls(v7) =>  (case  v26
                    of  Ln =>  (Ls(v7))
                    |   (Ls(v1)) =>  Ln
                    |   (Bn(v3,v2)) =>  (Ls(v7))
                    |   (Bs(v6,v5,v4)) =>  Ln)
    |   Bn(v15,v14) =>  (case  v26
                         of  Ln =>  (Bn(v15,v14))
                         |   (Ls(v8)) =>  (Bn(v15,v14))
                         |   (Bn(v10,v9)) =>  (mk_bn (difference v15 v10) (difference v14 v9))
                         |   (Bs(v13,v12,v11)) =>  (mk_bn (difference v15 v13) (difference v14 v11)))
    |   Bs(v24,v23,v22) =>  (case  v26
                             of  Ln =>  (Bs(v24,v23,v22))
                             |   (Ls(v16)) =>  (Bn(v24,v22))
                             |   (Bn(v18,v17)) =>  (mk_bs (difference v24 v18) v23 (difference v22 v17))
                             |   (Bs(v21,v20,v19)) =>  (mk_bn (difference v24 v21) (difference v22 v19)));

  fun  option_filter v4 =
    case  v4
    of  []  =>  []
     |   v3::v2 =>  (case  v3
                     of  NONE =>  (option_filter v2)
                     |   (SOME(v1)) =>  (v1::(option_filter v2)));

  fun  george_ok v13 =
    (fn  v15 =>
      (fn  v14 =>
        (fn  v16 =>
          let val  v12 = v16
           in
            case  v12
            of  (v11,v10) =>  (case  (lookup v11 v13)
                               of  NONE =>  (0 < 0)
                               |   (SOME(v9)) =>  (case  (lookup v10 v13)
                                                   of  NONE =>  (0 < 0)
                                                   |   (SOME(v8)) =>  (let val  v7 =
                                                                         difference v8 v9
                                                                           val  v3 =
                                                                         map (fn  v6 =>
                                                                               (case  v6
                                                                                of  (v5,v4) =>  (lookup v5 v14))) (toalist v7)
                                                                           val  v2 =
                                                                         option_filter v3
                                                                        in
                                                                         every (fn  v1 =>
                                                                                 (v1 < v15)) v2
                                                                        end)))
          end)));

  fun  union v25 v26 =
    case  v25
    of  Ln =>  v26
    |   Ls(v7) =>  (case  v26
                    of  Ln =>  (Ls(v7))
                    |   (Ls(v1)) =>  (Ls(v7))
                    |   (Bn(v3,v2)) =>  (Bs(v3,v7,v2))
                    |   (Bs(v6,v5,v4)) =>  (Bs(v6,v7,v4)))
    |   Bn(v15,v14) =>  (case  v26
                         of  Ln =>  (Bn(v15,v14))
                         |   (Ls(v8)) =>  (Bs(v15,v8,v14))
                         |   (Bn(v10,v9)) =>  (Bn(union v15 v10,union v14 v9))
                         |   (Bs(v13,v12,v11)) =>  (Bs(union v15 v13,v12,union v14 v11)))
    |   Bs(v24,v23,v22) =>  (case  v26
                             of  Ln =>  (Bs(v24,v23,v22))
                             |   (Ls(v16)) =>  (Bs(v24,v23,v22))
                             |   (Bn(v18,v17)) =>  (Bs(union v24 v18,v23,union v22 v17))
                             |   (Bs(v21,v20,v19)) =>  (Bs(union v24 v21,v23,union v22 v19)));

  fun  briggs_ok v13 =
    (fn  v15 =>
      (fn  v14 =>
        (fn  v16 =>
          let val  v12 = v16
           in
            case  v12
            of  (v11,v10) =>  (case  (lookup v11 v13)
                               of  NONE =>  (0 < 0)
                               |   (SOME(v9)) =>  (case  (lookup v10 v13)
                                                   of  NONE =>  (0 < 0)
                                                   |   (SOME(v8)) =>  (let val  v7 =
                                                                         union v9 v8
                                                                           val  v3 =
                                                                         map (fn  v6 =>
                                                                               (case  v6
                                                                                of  (v5,v4) =>  (lookup v5 v14))) (toalist v7)
                                                                           val  v2 =
                                                                         option_filter v3
                                                                        in
                                                                         (length (filter (fn  v1 =>
                                                                                           (v1 >= v15)) v2)) < v15
                                                                        end)))
          end)));

  fun  is_coalesceable_move v6 =
    (fn  v8 =>
      (fn  v7 =>
        (fn  v9 =>
          let val  v5 = v9
           in
            case  v5
            of  (v4,v3) =>  (case  v3
                             of  (v2,v1) =>  (if  (is_phy_var v2)
                                              then  (george_ok v6 v8 v7 (v2,v1))
                                              else  (briggs_ok v6 v8 v7 (v2,v1))))
          end)));

  fun  set_avail_moves_pri v2 =
    (fn  v1 => ((),ra_state_avail_moves_pri_fupd (k v2) v1));

  fun  add_unavail_moves v2 =
    (fn  v1 =>
      ((),ra_state_unavail_moves_fupd (k (append v2 (ra_state_unavail_moves v1))) v1));

  fun  get_avail_moves v1 =  unit (ra_state_avail_moves v1) v1;

  fun  set_avail_moves v2 =
    (fn  v1 => ((),ra_state_avail_moves_fupd (k v2) v1));

  fun  add_coalesce v2 =
    (fn  v3 =>
      (fn  v1 =>
        ((),ra_state_coalesced_fupd (k (insert v3 v2 (ra_state_coalesced v1))) v1)));

  fun  get_edges v2 =
    (fn  v1 => unit (lookup v2 (ra_state_graph v1)) v1);

  fun  inc_one v3 =
    bind (get_deg v3) (fn  v2 =>
                        (case  v2
                         of  NONE =>  (unit ())
                         |   (SOME(v1)) =>  (set_deg v3 (v1 + 1))));

  fun  dir_g_insert v4 =
    (fn  v5 =>
      (fn  v3 =>
        let val  v1 =
          case  (lookup v4 v3)
          of  NONE =>  (insert v5 () Ln)
          |   SOME(v2) =>  (insert v5 () v2)
        in
          insert v4 v1 v3
         end));

  fun  undir_g_insert v2 =
    (fn  v3 => (fn  v1 => dir_g_insert v2 v3 (dir_g_insert v3 v2 v1)));

  fun  force_add v2 =
    (fn  v3 =>
      (fn  v1 =>
        ((),ra_state_graph_fupd (k (undir_g_insert v2 v3 (ra_state_graph v1))) v1)));

  fun  do_coalesce v13 =
    let val  v12 = v13
     in
      case  v12
      of  (v11,v10) =>  (ignore_bind (add_coalesce v11 v10) (bind (get_edges v10) (fn  v9 =>
                                                                                    (bind (get_edges v11) (fn  v8 =>
                                                                                                            (bind get_degs (fn  v7 =>
                                                                                                                             (bind get_colours (fn  v6 =>
                                                                                                                                                 (case  v9
                                                                                                                                                  of  NONE =>  (unit ())
                                                                                                                                                  |   (SOME(v5)) =>  (case  v8
                                                                                                                                                                      of  NONE =>  (unit ())
                                                                                                                                                                      |   (SOME(v4)) =>  (let val  v2 =
                                                                                                                                                                                            filter (fn  v3 =>
                                                                                                                                                                                                     ((((lookup v3 v7) = NONE) = (0 < 0)) orelse  ((is_phy_var v3) andalso  (v3 < (2 * v6))))) (map fst (toalist v5))
                                                                                                                                                                                          in
                                                                                                                                                                                            foreach (v2,(fn  v1 =>
                                                                                                                                                                                                          if  ((lookup v1 v4) = NONE)
                                                                                                                                                                                                          then  (ignore_bind (inc_one v11) (force_add v11 v1))
                                                                                                                                                                                                          else  (dec_one v1)))
                                                                                                                                                                                          end))))))))))))
    end;

  fun  pair_rename v10 =
    (fn  v8 =>
      (fn  v9 =>
        let val  v7 = v9
         in
          case  v7
          of  (v6,v5) =>  (case  v5
                           of  (v4,v3) =>  (let val  v2 =
                                              if  (v4 = v8)
                                              then  v10
                                               else  v4
                                                val  v1 =
                                              if  (v3 = v8)
                                              then  v10
                                               else  v3
                                             in
                                              (v6,(v2,v1))
                                            end))
        end));

  fun  get_freeze_worklist v1 =  unit (ra_state_freeze_worklist v1) v1;

  fun  add_spill_worklist v2 =
    (fn  v1 =>
      ((),ra_state_spill_worklist_fupd (k (append v2 (ra_state_spill_worklist v1))) v1));

  fun  set_freeze_worklist v2 =
    (fn  v1 => ((),ra_state_freeze_worklist_fupd (k v2) v1));

  fun  respill v6 =
    bind get_colours (fn  v5 =>
                       (bind (get_deg v6) (fn  v4 =>
                                            (case  v4
                                             of  NONE =>  (unit ())
                                             |   (SOME(v3)) =>  (if  (v3 < v5)
                                                                 then  (unit ())
                                                                 else  (bind get_freeze_worklist (fn  v2 =>
                                                                                                   (if  (member v6 v2)
                                                                                                    then  (ignore_bind (add_spill_worklist [v6]) (set_freeze_worklist (filter (fn  v1 =>
                                                                                                                                                                                ((v1 = v6) = (0 < 0))) v2)))
                                                                                                    else  (unit ())))))))));

  fun  coalesce v29 =
    bind get_graph (fn  v28 =>
                     (bind get_colours (fn  v27 =>
                                         (bind get_degs (fn  v26 =>
                                                          (bind get_move_rel (fn  v25 =>
                                                                               (bind get_avail_moves_pri (fn  v24 =>
                                                                                                           (bind (case  (split_avail (is_valid_move v28 v25) (is_coalesceable_move v28 v27 v26) v24 [] )
                                                                                                                  of  (v4,v3) =>  (case  v3
                                                                                                                                   of  (v2,v1) =>  (ignore_bind (set_avail_moves_pri v1) (ignore_bind (add_unavail_moves v2) (unit v4))))) (fn  v23 =>
                                                                                                                                                                                                                                             (bind (case  v23
                                                                                                                                                                                                                                                    of  NONE =>  (bind get_avail_moves (fn  v9 =>
                                                                                                                                                                                                                                                                                         (case  (split_avail (is_valid_move v28 v25) (is_coalesceable_move v28 v27 v26) v9 [] )
                                                                                                                                                                                                                                                                                          of  (v8,v7) =>  (case  v7
                                                                                                                                                                                                                                                                                                           of  (v6,v5) =>  (ignore_bind (set_avail_moves v5) (ignore_bind (add_unavail_moves v6) (unit v8)))))))
                                                                                                                                                                                                                                                    |   (SOME(v10)) =>  (unit v23)) (fn  v22 =>
                                                                                                                                                                                                                                                                                      (case  v22
                                                                                                                                                                                                                                                                                       of  NONE =>  (unit NONE)
                                                                                                                                                                                                                                                                                       |   (SOME(v21)) =>  (case  v21
                                                                                                                                                                                                                                                                                                            of  (v20,v19) =>  (case  v19
                                                                                                                                                                                                                                                                                                                               of  (v18,v17) =>  (ignore_bind (do_coalesce (v18,v17)) (bind get_avail_moves_pri (fn  v16 =>
                                                                                                                                                                                                                                                                                                                                                                                                                  (bind get_avail_moves (fn  v15 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          (bind get_unavail_moves (fn  v14 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (let val  v13 =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       map (pair_rename v18 v17) v16
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         val  v12 =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       map (pair_rename v18 v17) v15
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         val  v11 =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       map (pair_rename v18 v17) v14
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      in
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       ignore_bind (set_avail_moves_pri v13) (ignore_bind (set_avail_moves v12) (ignore_bind (set_unavail_moves v11) (ignore_bind unspill (ignore_bind (respill v18) (unit (SOME(v17)))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     end)))))))))))))))))))))))) v29;

  fun  in_moves v7 v8 =
    case  v7
    of  []  =>  (0 < 0)
    |   v6::v5 =>  (case  v6
                    of  (v4,v3) =>  (case  v3
                                     of  (v2,v1) =>  ((v2 = v8) orelse  ((v1 = v8) orelse  (in_moves v5 v8)))));

  fun  in_moves_set v4 v5 =
    case  v5
    of  []  =>  Ln
    |   v3::v2 =>  (let val  v1 = in_moves_set v4 v2
                     in
                      if  (in_moves v4 v3)
                      then  (insert v3 () v1)
                      else  v1
                     end);

  fun  get_coalesced v1 =  unit (ra_state_coalesced v1) v1;

  fun  set_move_rel v2 =
    (fn  v1 => ((),ra_state_move_related_fupd (k v2) v1));

  fun  freeze v27 =
    bind get_freeze_worklist (fn  v26 =>
                               (bind get_unavail_moves (fn  v25 =>
                                                         (bind get_graph (fn  v24 =>
                                                                           (bind (unit (filter (fn  v5 =>
                                                                                                 (case  v5
                                                                                                  of  (v4,v3) =>  (case  v3
                                                                                                                   of  (v2,v1) =>  (((v2 = v1) = (0 < 0)) andalso  ((lookup_g v2 v1 v24) = (0 < 0)))))) v25)) (fn  v23 =>
                                                                                                                                                                                                                (bind get_degs (fn  v22 =>
                                                                                                                                                                                                                                 (bind (unit (in_moves_set v23 (map fst (toalist v22)))) (fn  v21 =>
                                                                                                                                                                                                                                                                                           (bind get_coalesced (fn  v20 =>
                                                                                                                                                                                                                                                                                                                 (bind (unit (filter (fn  v6 =>
                                                                                                                                                                                                                                                                                                                                       ((lookup v6 v20) = NONE)) v26)) (fn  v19 =>
                                                                                                                                                                                                                                                                                                                                                                         (bind (set_move_rel v21) (fn  v18 =>
                                                                                                                                                                                                                                                                                                                                                                                                    (bind (set_unavail_moves v23) (fn  v17 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                    (bind (let val  v13 =
                                                                                                                                                                                                                                                                                                                                                                                                                                             partition (fn  v14 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                         ((lookup v14 v21) = (SOME(v17)))) v19
                                                                                                                                                                                                                                                                                                                                                                                                                                            in
                                                                                                                                                                                                                                                                                                                                                                                                                                             case  v13
                                                                                                                                                                                                                                                                                                                                                                                                                                             of  (v12,v11) =>  (case  v11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                of  []  =>  (case  v12
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             of  []  =>  (unit NONE)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |   (v8::v7) =>  (ignore_bind (set_freeze_worklist v7) (unit (SOME(v8)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                |   (v10::v9) =>  (ignore_bind (add_simp_worklist v9) (ignore_bind (set_freeze_worklist v12) (unit (SOME(v10))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                           end) (fn  v16 =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (case  v16
                                                                                                                                                                                                                                                                                                                                                                                                                                                   of  NONE =>  (unit NONE)
                                                                                                                                                                                                                                                                                                                                                                                                                                                   |   (SOME(v15)) =>  (ignore_bind (dec_deg v15) (ignore_bind unspill (unit (SOME(v15))))))))))))))))))))))))))) v27;

  fun  max_non_coalesced v16 v17 v18 v19 v20 =
    case  (v17,(v18,(v19,v20)))
    of  (v15,v14) =>  (case  v14
                       of  (v13,v12) =>  (case  v13
                                          of  []  =>  (case  v12
                                                       of  (v4,v3) =>  (case  v3
                                                                        of  (v2,v1) =>  (v2,v4)))
                                          |   (v11::v10) =>  (case  v12
                                                              of  (v9,v8) =>  (case  v8
                                                                               of  (v7,v6) =>  (if  ((lookup v11 v16) = NONE)
                                                                                                then  (case  (lookup v11 v15)
                                                                                                       of  NONE =>  (max_non_coalesced v16 v15 v10 v9 (v7,v6))
                                                                                                       |   (SOME(v5)) =>  (if  (v5 > v6)
                                                                                                                           then  (max_non_coalesced v16 v15 v10 (v7::v9) (v11,v5))
                                                                                                                           else  (max_non_coalesced v16 v15 v10 (v11::v9) (v7,v6))))
                                                                                                else  (max_non_coalesced v16 v15 v10 v9 (v7,v6)))))));

  fun  spill v11 =
    bind get_spill_worklist (fn  v10 =>
                              (bind get_coalesced (fn  v9 =>
                                                    (bind get_degs (fn  v8 =>
                                                                     (case  v10
                                                                      of  []  =>  (unit NONE)
                                                                      |   (v7::v6) =>  (bind (unit (case  (lookup v7 v8)
                                                                                                    of  NONE =>  0
                                                                                                    |   (SOME(v1)) =>  v1)) (fn  v5 =>
                                                                                                                              (bind (unit (max_non_coalesced v9 v8 v6 [] (v7,v5))) (fn  v4 =>
                                                                                                                                                                                     (case  v4
                                                                                                                                                                                      of  (v3,v2) =>  (ignore_bind (set_spill_worklist v2) (ignore_bind (dec_deg v3) (ignore_bind unspill (unit (SOME(v3))))))))))))))))) v11;

  fun  delete v7 v8 =
    case  v8
    of  Ln =>  Ln
    |   Ls(v1) =>  (if  (v7 <= 0)
                    then  Ln
                     else  (Ls(v1)))
    |   Bn(v3,v2) =>  (if  (v7 <= 0)
                       then  (Bn(v3,v2))
                       else  (if  (even v7)
                              then  (mk_bn (delete ((let val  k = v7 - 1
                                                      in
                                                       if  (k < 0)
                                                       then  0
                                                        else  k
                                                      end) div 2) v3) v2)
                              else  (mk_bn v3 (delete ((let val  k =
                                                          v7 - 1
                                                         in
                                                          if  (k < 0)
                                                          then  0
                                                           else  k
                                                         end) div 2) v2))))
    |   Bs(v6,v5,v4) =>  (if  (v7 <= 0)
                          then  (Bn(v6,v4))
                          else  (if  (even v7)
                                 then  (mk_bs (delete ((let val  k =
                                                          v7 - 1
                                                         in
                                                          if  (k < 0)
                                                          then  0
                                                           else  k
                                                         end) div 2) v6) v5 v4)
                                 else  (mk_bs v6 v5 (delete ((let val  k =
                                                                v7 - 1
                                                               in
                                                                if  (k < 0)
                                                                then  0
                                                                 else  k
                                                               end) div 2) v4))));

  fun  push_stack v2 =
    (fn  v1 =>
      ((),ra_state_degs_fupd (k (delete v2 (ra_state_degs v1))) (ra_state_stack_fupd (k (v2::(ra_state_stack v1))) (ra_state_move_related_fupd (k (delete v2 (ra_state_move_related v1))) v1))));

  fun  do_step v9 =
    ignore_bind dec_clock (bind simplify (fn  v8 =>
                                           (case  v8
                                            of  NONE =>  (bind coalesce (fn  v6 =>
                                                                          (case  v6
                                                                           of  NONE =>  (bind freeze (fn  v4 =>
                                                                                                       (case  v4
                                                                                                        of  NONE =>  (bind spill (fn  v2 =>
                                                                                                                                   (case  v2
                                                                                                                                    of  NONE =>  (unit ())
                                                                                                                                    |   (SOME(v1)) =>  (push_stack v1))))
                                                                                                        |   (SOME(v3)) =>  (push_stack v3))))
                                                                           |   (SOME(v5)) =>  (push_stack v5))))
                                            |   (SOME(v7)) =>  (push_stack v7)))) v9;

  fun  rpt_do_step v1 =
    ((),while_1 (o_1 fst has_work) (o_1 snd do_step) v1);

  fun  deg_comparator v3 =
    (fn  v4 =>
      (fn  v5 =>
        case  (lookup v4 v3)
        of  NONE =>  (0 <= 0)
        |   SOME(v2) =>  (case  (lookup v5 v3)
                          of  NONE =>  (0 <= 0)
                          |   (SOME(v1)) =>  (v2 <= v1))));

  fun  full_simplify v5 =
    bind get_simp_worklist (fn  v4 =>
                             (bind get_degs (fn  v3 =>
                                              (case  (qsort (deg_comparator v3) v4)
                                               of  []  =>  (unit NONE)
                                               |   (v2::v1) =>  (ignore_bind (set_simp_worklist v1) (ignore_bind (dec_deg v2) (unit (SOME(v2))))))))) v5;

  fun  do_step2 v3 =
    ignore_bind dec_clock (bind full_simplify (fn  v2 =>
                                                (case  v2
                                                 of  NONE =>  (unit ())
                                                 |   (SOME(v1)) =>  (push_stack v1)))) v3;

  fun  rpt_do_step2 v1 =
    ((),while_1 (o_1 fst has_work) (o_1 snd do_step2) v1);

  fun  briggs_has_work v4 =
    bind get_clock (fn  v3 =>
                     (bind get_avail_moves (fn  v2 =>
                                             (bind get_avail_moves_pri (fn  v1 =>
                                                                         (unit ((v3 > 0) andalso  (((v2 = [] ) = (0 < 0)) orelse  ((v1 = [] ) = (0 < 0)))))))))) v4;

  fun  do_briggs_step v3 =
    ignore_bind dec_clock (bind coalesce (fn  v2 =>
                                           (case  v2
                                            of  NONE =>  (unit ())
                                            |   (SOME(v1)) =>  (push_stack v1)))) v3;

  fun  briggs_coalesce v1 =
    ((),snd (set_unavail_moves [] (snd (set_move_rel Ln (while_1 (o_1 fst briggs_has_work) (o_1 snd do_briggs_step) v1)))));

  fun  is_alloc_var v1 =  (v1 mod 4) = 1;

  fun  considered_var v1 =
    (fn  v2 =>
      (is_alloc_var v2) orelse  ((is_phy_var v2) andalso  (v2 < (2 * v1))));

  fun  count_degrees v1 =
    (fn  v2 => length (filter v1 (map fst (toalist v2))));

  fun  fromalist v5 =
    case  v5
    of  []  =>  Ln
    |   v4::v3 =>  (case  v4
                    of  (v2,v1) =>  (insert v2 v1 (fromalist v3)));

  fun  init_ra_state v32 =
    (fn  v33 =>
      (fn  v34 =>
        let val  v26 =
          filter (fn  v31 =>
                   (case  v31
                    of  (v30,v29) =>  (case  v29
                                       of  (v28,v27) =>  ((considered_var v33 v28) andalso  (considered_var v33 v27))))) v34
            val  v25 = filter is_alloc_var (map fst (toalist v32))
            val  v23 =
          map (fn  v24 =>
                (v24,count_degrees (considered_var v33) (the (lookup v24 v32)))) v25
            val  v22 = fromalist v23
            val  v18 =
          partition (fn  v21 =>
                      (case  v21 of  (v20,v19) =>  (v19 < v33))) v23
         in
          case  v18
          of  (v17,v16) =>  (let val  v15 = in_moves_set v26 v25
                                 val  v9 =
                               partition (fn  v14 =>
                                           (case  v14
                                            of  (v13,v12) =>  (case  v12
                                                               of  (v11,v10) =>  (v13 > 0)))) v26
                              in
                               case  v9
                               of  (v8,v7) =>  (let val  v3 =
                                                  partition (fn  v6 =>
                                                              (case  v6
                                                               of  (v5,v4) =>  ((lookup v5 v15) = (let val  x =
                                                                                                     ()
                                                                                                   in
                                                                                                     SOME(x)
                                                                                                   end)))) v17
                                                 in
                                                  case  v3
                                                  of  (v2,v1) =>  (Recordtypera_state(v32,v33,v22,map fst v1,map fst v2,map fst v16,[] ,Ln,v15,v8,v7,[] ,length v25))
                                                end)
                             end)
        end));

  fun  sec_ra_state v10 =
    (fn  v8 =>
      (fn  v9 =>
        (fn  v11 =>
          let val  v6 =
            filter (fn  v7 => (((lookup v7 v10) = NONE) = (0 < 0))) v9
              val  v3 =
            map (fn  v5 =>
                  (v5,count_degrees (fn  v4 =>
                                      (((is_phy_var v4) andalso  (v4 >= (2 * v8))) orelse  (member v4 v6))) (the (lookup v5 v10)))) v6
              val  v2 = fromalist v3
              val  v1 = map fst (toalist v11)
          in
            Recordtypera_state(v10,v8,v2,v6,[] ,[] ,v1,Ln,Ln,[] ,[] ,[] ,length v6)
          end)));

  fun  maybe_flip v6 =
    let val  v5 = v6
     in
      case  v5
      of  (v4,v3) =>  (case  v3
                       of  (v2,v1) =>  (if  (is_phy_var v2)
                                        then  (v4,(v2,v1))
                                        else  (v4,(v1,v2))))
    end;

  fun  first_match_col v8 v7 v9 =
    case  v9
    of  []  =>  NONE
    |   v6::v5 =>  (let val  v4 = v6
                     in
                      case  v4
                      of  (v3,v2) =>  (case  (lookup v2 v7)
                                       of  NONE =>  (first_match_col v8 v7 v5)
                                       |   (SOME(v1)) =>  (if  (member v1 v8)
                                                           then  (SOME(v1))
                                                           else  (first_match_col v8 v7 v5)))
                    end);

  fun  move_pref v4 =
    (fn  v5 =>
      (fn  v3 =>
        (fn  v2 =>
          case  (lookup v5 v4)
          of  NONE =>  NONE
          |   SOME(v1) =>  (first_match_col v3 v2 v1))));

  fun  resort_moves v12 =
    let val  v11 = toalist v12
        val  v1 =
      map (fn  v10 =>
            (case  v10
             of  (v9,v8) =>  (v9,qsort (fn  v7 =>
                                         (case  v7
                                          of  (v6,v5) =>  (fn  v4 =>
                                                           (case  v4
                                                            of  (v3,v2) =>  (v6 > v3))))) v8))) v11
     in
      fromalist v1
     end;

  fun  pri_move_insert v3 =
    (fn  v4 =>
      (fn  v5 =>
        (fn  v2 =>
          case  (lookup v4 v2)
          of  NONE =>  (insert v4 [(v3,v5)] v2)
          |   SOME(v1) =>  (insert v4 ((v3,v5)::v1) v2))));

  fun  undir_move_insert v2 =
    (fn  v3 =>
      (fn  v4 =>
        (fn  v1 =>
          pri_move_insert v2 v3 v4 (pri_move_insert v2 v4 v3 v1))));

  fun  moves_to_sp v9 v8 =
    case  v9
    of  []  =>  v8
    |   v7::v6 =>  (let val  v5 = v7
                     in
                      case  v5
                      of  (v4,v3) =>  (case  v3
                                       of  (v2,v1) =>  (moves_to_sp v6 (undir_move_insert v4 v2 v1 v8)))
                    end);

  fun  aux_pref v5 =
    (fn  v6 =>
      (fn  v4 =>
        (fn  v3 =>
          case  (lookup v6 v5)
          of  NONE =>  NONE
          |   SOME(v2) =>  (case  (lookup v2 v3)
                            of  NONE =>  NONE
                            |   (SOME(v1)) =>  (if  (member v1 v4)
                                                then  (SOME(v1))
                                                else  NONE)))));

  fun  aux_move_pref v3 =
    (fn  v5 =>
      (fn  v6 =>
        (fn  v4 =>
          (fn  v2 =>
            case  (aux_pref v3 v6 v4 v2)
            of  NONE =>  (move_pref v5 v6 v4 v2)
            |   SOME(v1) =>  (SOME(v1))))));

  fun  id_colour v3 =
    foldr (fn  v2 => (fn  v1 => (insert v2 v2 v1))) Ln v3;

  fun  remove_colours v9 v10 v8 =
    case  v8
    of  []  =>  []
     |   v7::v6 =>  (case  v10
                     of  []  =>  (v7::v6)
                     |   (v5::v4) =>  (let val  v3 = lookup v5 v9
                                        in
                                         case  v3
                                         of  NONE =>  (remove_colours v9 v4 (v7::v6))
                                         |   SOME(v2) =>  (remove_colours v9 v4 (filter (fn  v1 =>
                                                                                          ((v1 = v2) = (0 < 0))) (v7::v6)))
                                       end));

  fun  assign_colour v14 =
    (fn  v10 =>
      (fn  v11 =>
        (fn  v13 =>
          (fn  v9 =>
            (fn  v12 =>
              case  (lookup v13 v9)
              of  NONE =>  (if  (member v13 v12)
                            then  (v9,v12)
                            else  (case  (lookup v13 v14)
                                   of  NONE =>  (v9,v12)
                                   |   (SOME(v7)) =>  (if  (is_alloc_var v13)
                                                       then  (let val  v6 =
                                                                map fst (toalist v7)
                                                                  val  v5 =
                                                                remove_colours v9 v6 v10
                                                               in
                                                                case  v5
                                                                of  []  =>  (v9,v13::v12)
                                                                |   v4::v3 =>  (let val  v1 =
                                                                                  case  (v11 v13 (v4::v3) v9)
                                                                                  of  NONE =>  v4
                                                                                  |   SOME(v2) =>  v2
                                                                                 in
                                                                                  (insert v13 v1 v9,v12)
                                                                                end)
                                                              end)
                                                       else  (v9,v13::v12))))
              |   SOME(v8) =>  (v9,v12))))));

  fun  alloc_colouring_aux v8 v10 v6 v11 v9 v7 =
    case  v11
    of  []  =>  (v9,v7)
    |   v5::v4 =>  (let val  v3 = assign_colour v8 v10 v6 v5 v9 v7
                     in
                      case  v3
                      of  (v2,v1) =>  (alloc_colouring_aux v8 v10 v6 v4 v2 v1)
                    end);

  fun  alloc_colouring v11 =
    (fn  v12 =>
      (fn  v14 =>
        (fn  v13 =>
          let val  v10 = map fst (toalist v11)
              val  v9 = partition is_phy_var v10
           in
            case  v9
            of  (v8,v7) =>  (let val  v6 = id_colour v8
                                 val  v4 =
                               genlist (fn  v5 => (2 * v5)) v12
                                 val  v3 =
                               alloc_colouring_aux v11 v4 v14 v13 v6 []
                              in
                               case  v3
                               of  (v2,v1) =>  (alloc_colouring_aux v11 v4 v14 v7 v2 v1)
                             end)
          end)));

  fun  list_g_insert v6 v5 v4 =
    case  v5
    of  []  =>  (case  (lookup v6 v4)
                 of  NONE =>  (insert v6 Ln v4)
                 |   (SOME(v1)) =>  v4)
    |   v3::v2 =>  (undir_g_insert v6 v3 (list_g_insert v6 v2 v4));

  fun  full_coalesce_aux v16 v18 v17 =
    case  v17
    of  []  =>  (v16,Ln)
    |   v15::v14 =>  (let val  v13 = v15
                       in
                        case  v13
                        of  (v12,v11) =>  (case  v11
                                           of  (v10,v9) =>  (if  ((lookup_g v10 v9 v16) orelse  ((lookup v10 v16) = NONE))
                                                             then  (full_coalesce_aux v16 v18 v14)
                                                             else  (case  (lookup v9 v16)
                                                                    of  NONE =>  (full_coalesce_aux v16 v18 v14)
                                                                    |   (SOME(v8)) =>  (let val  v6 =
                                                                                          filter (fn  v7 =>
                                                                                                   (member v7 v18)) (map fst (toalist v8))
                                                                                            val  v5 =
                                                                                          list_g_insert v10 v6 v16
                                                                                            val  v4 =
                                                                                          map (pair_rename v10 v9) v14
                                                                                            val  v3 =
                                                                                          full_coalesce_aux v5 v18 v14
                                                                                         in
                                                                                          case  v3
                                                                                          of  (v2,v1) =>  (v2,insert v9 v10 v1)
                                                                                        end))))
                      end);

  fun  full_coalesce v22 =
    (fn  v23 =>
      (fn  v24 =>
        (fn  v25 =>
          let val  v16 =
            filter (fn  v21 =>
                     (case  v21
                      of  (v20,v19) =>  (case  v19
                                         of  (v18,v17) =>  (((member v18 v25) orelse  ((is_phy_var v18) andalso  (v18 >= (2 * v23)))) andalso  (member v17 v25))))) v24
              val  v5 =
            qsort (fn  v15 =>
                    (case  v15
                     of  (v14,v13) =>  (case  v13
                                        of  (v12,v11) =>  (fn  v10 =>
                                                           (case  v10
                                                            of  (v9,v8) =>  (case  v8
                                                                             of  (v7,v6) =>  (v14 > v9))))))) v16
              val  v4 = full_coalesce_aux v22 v25 v5
           in
            case  v4
            of  (v3,v2) =>  (v3,(filter (fn  v1 =>
                                          ((lookup v1 v2) = NONE)) v25,v2))
          end)));

  fun  unbound_colours v3 v4 =
    case  v4
    of  []  =>  v3
    |   v2::v1 =>  (if  (v3 < v2)
                    then  v3
                     else  (if  (v2 = v3)
                            then  (unbound_colours (v3 + 2) v1)
                            else  (unbound_colours v3 v1)));

  fun  assign_colour2 v13 =
    (fn  v15 =>
      (fn  v16 =>
        (fn  v17 =>
          (fn  v14 =>
            case  (lookup v17 v14)
            of  NONE =>  (case  (lookup v17 v13)
                          of  NONE =>  v14
                          |   (SOME(v11)) =>  (let val  v10 =
                                                 map fst (toalist v11)
                                                   val  v8 =
                                                 option_filter (map (fn  v9 =>
                                                                      (lookup v9 v14)) v10)
                                                   val  v5 =
                                                 case  (lookup v17 v16)
                                                 of  NONE =>  NONE
                                                 |   SOME(v7) =>  (case  (lookup v7 v14)
                                                                   of  NONE =>  NONE
                                                                   |   (SOME(v6)) =>  (if  ((member v6 v8) orelse  (((is_phy_var v6) = (0 < 0)) orelse  ((v6 >= (2 * v15)) = (0 < 0))))
                                                                                       then  NONE
                                                                                        else  (SOME(v6))))
                                                   val  v1 =
                                                 case  v5
                                                 of  NONE =>  (unbound_colours (2 * v15) (qsort (fn  v3 =>
                                                                                                  (fn  v2 =>
                                                                                                    (v3 <= v2))) v8))
                                                 |   SOME(v4) =>  v4
                                                in
                                                 insert v17 v1 v14
                                                end))
            |   SOME(v12) =>  v14))));

  fun  spill_colouring v4 v6 v8 v7 v5 =
    case  v7
    of  []  =>  v5
    |   v3::v2 =>  (let val  v1 = assign_colour2 v4 v6 v8 v3 v5
                     in
                      spill_colouring v4 v6 v8 v2 v1
                     end);

  val reg_alloc_verbose = ref true

  fun mk_unique [] = []
  |   mk_unique (x::xs) = x::mk_unique(filter (fn y => x=x) xs)

  fun  reg_alloc v25 =
    (fn  v24 =>
      (fn  v26 =>
        (fn  v27 =>
          let val  v23 = map maybe_flip v27
              val  v19 =
            if  (v25 <= 0)
            then  (init_ra_state v24 v26 [] )
            else  (if  (v25 = 1)
                   then  (let val  v22 =
                            briggs_coalesce (init_ra_state v24 v26 v23)
                          in
                            case  v22 of  (v21,v20) =>  v20
                           end)
                   else  (if  (v25 = 2)
                          then  (init_ra_state v24 v26 v23)
                          else  (init_ra_state v24 v26 v23)))
              val  v18 = rpt_do_step v19
           in
            case  v18
            of  (v17,v16) =>  (let val  v15 =
                                 if  (v25 <= 0)
                                 then  (move_pref (resort_moves (moves_to_sp v23 Ln)))
                                 else  (if  (v25 = 1)
                                        then  (aux_move_pref (ra_state_coalesced v16) (resort_moves (moves_to_sp v23 Ln)))
                                        else  (if  (v25 = 2)
                                               then  (aux_pref (ra_state_coalesced v16))
                                               else  (aux_move_pref (ra_state_coalesced v16) (resort_moves (moves_to_sp v23 Ln)))))
                                   val  v14 =
                                 alloc_colouring (ra_state_graph v16) v26 v15 (ra_state_stack v16)
                               in
                                 case  v14
                                 of  (v13,v12) =>  (let val  v11 =
                                                      full_coalesce (ra_state_graph v16) v26 v23 v12
                                                     in
                                                      case  v11
                                                      of  (v10,v9) =>  (case  v9
                                                                        of  (v8,v7) =>  (let val  v6 =
                                                                                           sec_ra_state v10 v26 v8 v7
                                                                                             val  v5 =
                                                                                           rpt_do_step2 v6
                                                                                          in
                                                                                           case  v5
                                                                                           of  (v4,v3) =>  (let val  v2 =
                                                                                                              spill_colouring v10 v26 v7 (ra_state_stack v3) v13
                                                                                                             in
                                                                                                              let val col = spill_colouring v10 v26 Ln v12 v2
                                                                                                                  val moves = map snd v23
                                                                                                                  val gmoves = filter (fn (v1,v2) => (((v2 = v1) = (0 < 0)) andalso  ((lookup_g v2 v1 v24) = (0 < 0)))) moves
                                                                                                                  val cmoves = map (fn (v1,v2) => (the (lookup v1 col),the (lookup v2 col))) moves
                                                                                                                  val good_c = filter (fn (v1,v2) => v1 = v2) cmoves
                                                                                                                  val _ = (if !reg_alloc_verbose then
                                                                                                                            print(" "^Int.toString (length moves)^" "^Int.toString (length gmoves)^" "^Int.toString (length good_c)^"\n")
                                                                                                                          else
                                                                                                                            ()) in
                                                                                                                  col
                                                                                                                  end
                                                                                                             end)
                                                                                         end))
                                                    end)
                               end)
          end)));

  datatype reg_alloc_clash_tree =  Seq of  reg_alloc_clash_tree *  reg_alloc_clash_tree
                                |  Branch of  one sptree_spt option *  reg_alloc_clash_tree *  reg_alloc_clash_tree
                                |  Set of  one sptree_spt
                                |  Delta of  int list *  int list;

  fun  extend_clique v5 v4 v3 =
    case  v5
    of  []  =>  (v3,v4)
    |   v2::v1 =>  (if  (member v2 v4)
                    then  (extend_clique v1 v4 v3)
                    else  (extend_clique v1 (v2::v4) (list_g_insert v2 v4 v3)));

  fun  clique_g_insert v4 v3 =
    case  v4
    of  []  =>  v3
    |   v2::v1 =>  (list_g_insert v2 v1 (clique_g_insert v1 v3));

  fun  clash_tree_to_spg v30 v31 v29 =
    case  v30
    of  Delta(v10,v9) =>  (let val  v8 = extend_clique v10 v31 v29
                            in
                             case  v8
                             of  (v7,v6) =>  (let val  v4 =
                                                filter (fn  v5 =>
                                                         ((member v5 v10) = (0 < 0))) v6
                                                  val  v3 =
                                                extend_clique v9 v4 v7
                                               in
                                                case  v3
                                                of  (v2,v1) =>  (v2,v1)
                                              end)
                           end)
    |   Set(v12) =>  (let val  v11 = map fst (toalist v12)
                      in
                        (clique_g_insert v11 v29,v11)
                      end)
    |   Branch(v23,v22,v21) =>  (let val  v20 =
                                   clash_tree_to_spg v22 v31 v29
                                  in
                                   case  v20
                                   of  (v19,v18) =>  (let val  v17 =
                                                        clash_tree_to_spg v21 v31 v19
                                                       in
                                                        case  v17
                                                        of  (v16,v15) =>  (case  v23
                                                                           of  NONE =>  (extend_clique v18 v15 v16)
                                                                           |   (SOME(v14)) =>  (let val  v13 =
                                                                                                  map fst (toalist v14)
                                                                                                in
                                                                                                  (clique_g_insert v13 v16,v13)
                                                                                                end))
                                                      end)
                                 end)
    |   Seq(v28,v27) =>  (let val  v26 = clash_tree_to_spg v27 v31 v29
                           in
                            case  v26
                            of  (v25,v24) =>  (clash_tree_to_spg v28 v24 v25)
                          end);

end
